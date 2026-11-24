"""Emit the Lean round certificate of a wall (see docs/certificate-format.md).

    python3 -I certgen/emit_round.py CERT.json NAME OUTFILE [--lean-dir DIR] [--no-probe]

writes OUTFILE (module Cert.<NAME>.Round): the `CertD` literal of the steady rounds, `round_ok :
check cert = true := by decide +kernel`, `init_ok` glued to `Cert.<NAME>.Init.initial_run`, and the
wall theorem instance.  Two things are computed here and only then checked in Lean:
* the representative row tag `rt` of every step (a row of class j0; the Python side verifies the
  `eqTags` condition over j0 .. j0+2p-1 and the iterations, exactly like `tagOk`);
* the counter shift `d` of every cycle, by `probeD` (a Lean `#eval` on the same certificate).
"""
import sys, os, json, re, subprocess, tempfile


def lst(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def mv(m):
    k = m[0]
    if k == 'pull': return '.toRight %d' % m[1] if m[2] == 'R' else '.toLeft %d' % m[1]
    if k == 'abs': return '.fromRight %d' % m[1] if m[2] == 'R' else '.fromLeft %d' % m[1]
    if k == 'rot': return '.rot %d %d' % (m[1], m[2])
    if k == 'trot': return '.tailRot %d' % m[1]
    if k == 'tpull': return '.tailOut'
    if k == 'tabs': return '.tailIn'
    if k == 'fold': return '.split %d %d %d %d' % (m[1], m[2], len(m[4]), m[3])
    if k == 'drop': return '.expand %d 0' % m[1]
    raise ValueError(m)


def mvs(ms):
    return '[' + ', '.join(mv(m) for m in ms) + ']'


def shp(b, y, z):
    blocks = ', '.join('(%s, %s)' % (lst(y[i]), lst(b[i + 1])) for i in range(len(y)))
    return '⟨%s, [%s], %s⟩' % (lst(b[0]), blocks, lst(z))


def I(x):
    return '(%d : Int)' % x if x < 0 else str(x)


class Tags:
    def __init__(self, gpre, gper):
        self.gpre, self.gper = gpre, gper
        self.N, self.p = len(gpre), len(gper)

    def gv(self, x):
        return self.gpre[x] if x < self.N else self.gper[(x - self.N) % self.p]

    def rtag(self, a):
        return a if a < self.N else self.N + (a - self.N) % self.p

    def eq(self, x, rt):
        return all((self.gv(x) != self.gv(x + d)) == (self.gv(rt) != self.gv(rt + d))
                   for d in range(self.N + self.p))


def build(cert):
    w, law = cert['wall'], cert['law']
    R, k0 = cert['R'], cert['k0']
    T0 = cert['initial']['rows']
    al, be = law['alpha'], law['beta']
    tg = Tags(w['gpre'], w['gper'])
    p = tg.p
    T = {k0: T0}

    def t(k):
        assert k >= k0
        while max(T) < k:
            m = max(T)
            T[m + 1] = T[m] + al * m + be
        return T[k]

    out = []   # per class: (j0, init, cnt, phases as lean text with 'D' marker)
    for cl in cert['classes']:
        i, j0 = cl['i'], cl['j0']
        off = [0, 0]
        phs = []
        for ph in cl['phases']:
            if ph['kind'] == 'step':
                row = lambda j, t_, si: t(R * j + i) + off[0] * j + off[1] + si + t_ * 1
                rt = tg.rtag(row(j0, 0, 0))
                for u in range(2 * p):
                    if not tg.eq(row(j0 + u, 0, 0), rt):
                        raise SystemExit('tag class of class %d step at off %s varies with j' % (i, off))
                phs.append(('step', rt, ph['moves']))
                off[1] += 1
            else:
                ln, (ca, cb) = ph['len'], ph['count']
                rts = []
                for si in range(ln):
                    row = lambda j, t_, si=si: t(R * j + i) + off[0] * j + off[1] + si + t_ * ln
                    rt = tg.rtag(row(j0, 0))
                    for u in range(2 * p):
                        for t_ in range(p):
                            if not tg.eq(row(j0 + u, t_), rt):
                                raise SystemExit('tag class of class %d cycle row %d varies' % (i, si))
                    rts.append(rt)
                assert len(ph['steps']) == ln
                phs.append(('cycle', ln, ca, cb, rts, ph['steps']))
                off[0] += ln * ca
                off[1] += ln * cb
        assert off == list(cl['rows']) or True
        out.append((cl, phs, tuple(off)))
    return out, (T0, k0, R, al, be)


def phase_lean(ph, ds):
    if ph[0] == 'step':
        return '.step %d %s' % (ph[1], mvs(ph[2]))
    _, ln, ca, cb, rts, steps = ph
    d = ds.pop(0) if ds is not None else []
    return '.cycle %d %s %s [%s] %s [%s]' % (ln, I(ca), I(cb), ', '.join(I(x) for x in d), lst(rts),
                                             ', '.join(mvs(s) for s in steps))


def cn0_src(init):
    return '[' + ', '.join('⟨%s, 0, %s⟩' % (I(a), I(b)) for a, b in init['cnt']) + ']'


def make_cuts(phs, K):
    """chunk sizes (in phases): every cycle alone, steps in groups of at most K"""
    cuts, run = [], 0
    for ph in phs:
        if ph[0] == 'cycle':
            if run: cuts.append(run); run = 0
            cuts.append(1)
        else:
            run += 1
            if run == K: cuts.append(run); run = 0
    if run: cuts.append(run)
    return cuts


def chunk_defs(cert, out, ds_per_class, cuts_per_class, states_per_class):
    """Lean source of the chunk definitions; returns (text, names per class)"""
    text, names = [], []
    for (cl, phs, off), ds, cuts, sts in zip(out, ds_per_class, cuts_per_class, states_per_class):
        ds = None if ds is None else list(ds)
        init = cl['init']
        cur = (shp(init['b'], init['y'], init['z']), cn0_src(init), '(0, 0)')
        pos = 0
        nm = []
        for k, (n, st) in enumerate(zip(cuts, sts)):
            body = ',\n    '.join(phase_lean(ph, ds) for ph in phs[pos:pos + n])
            pos += n
            name = 'ch%d_%d' % (cl['i'], k)
            nm.append(name)
            if st is None:
                end = ('⟨[], [], []⟩', '[]', '(0, 0)')
            else:
                end = st
            text.append('def %s : Chunk :=\n  ⟨[%s],\n   %s, %s, %s,\n   %s, %s, %s⟩\n' %
                        (name, body, cur[0], cur[1], cur[2], end[0], end[1], end[2]))
            cur = end
        names.append(nm)
    return '\n'.join(text), names


def cert_def(cert, out, names):
    law = cert['law']
    T0 = cert['initial']['rows']
    lines = ['def cert : CertD where',
             '  S1 := S1', '  gpre := gpre', '  gper := gper',
             '  π := %d' % law['pi'], '  α := %d' % law['alpha'], '  β := %d' % law['beta'],
             '  Δ := %d' % law['delta'], '  w0 := %d' % law['w0'], '  c := %d' % law['c'],
             '  R := %d' % cert['R'], '  k0 := %d' % cert['k0'], '  T0 := %d' % T0,
             '  classes := [']
    cls = []
    for (cl, phs, off), nm in zip(out, names):
        init = cl['init']
        cnt = ', '.join('(%s, %s)' % (I(a), I(b)) for a, b in init['cnt'])
        cls.append('    ⟨%d, %s,\n     [%s],\n     [%s]⟩' % (cl['j0'], shp(init['b'], init['y'], init['z']),
                                                         cnt, ', '.join(nm)))
    lines.append(',\n'.join(cls) + ']')
    return '\n'.join(lines) + '\n'


def run_lean(src, lean_dir):
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False, dir=lean_dir) as f:
        f.write(src.replace('open Family\n', 'open Family\nset_option maxRecDepth 100000\n', 1))
        path = f.name
    try:
        r = subprocess.run(['lake', 'env', 'lean', path], cwd=lean_dir, capture_output=True, text=True)
    finally:
        os.unlink(path)
    return r


def run_probe(cert, out, lean_dir, name, K):
    ns = 'Family.Cert.%s' % name
    cuts = [make_cuts(phs, K) for (_, phs, _) in out]
    nones = [[None] * len(c) for c in cuts]
    defs, names = chunk_defs(cert, out, [None] * len(out), [[sum(c)] for c in cuts], [[None]] * len(out))
    src = 'import FamilyMain\nimport Cert.%s.Wall\nnamespace %s\nopen Family\n' % (name, ns)
    src += defs + '\n' + cert_def(cert, out, names)
    for i in range(cert['R']):
        src += '#eval probeRun cert %d %s\n' % (i, lst(cuts[i]))
    src += 'end %s\n' % ns
    r = run_lean(src, lean_dir)
    ds, sts, cur = [], [], None
    for line in r.stdout.splitlines():
        if line.startswith('D '):
            ds.append(json.loads(line[2:])); sts.append([])
        elif line.startswith('S '):
            sh, cn, off = line[2:].split(' | ')
            sts[-1].append((sh, cn, off))
        elif line.startswith('FAIL'):
            raise SystemExit('probe: ' + line + '\n' + r.stdout[-2000:])
    if len(ds) != cert['R'] or any(len(a) != len(c) for a, c in zip(sts, cuts)):
        raise SystemExit('probe output unparsed:\n' + r.stdout[-3000:] + r.stderr[-3000:])
    return ds, cuts, sts


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    K = 25
    for a in sys.argv[1:]:
        if a.startswith('--K='): K = int(a[4:])
    cert = json.load(open(args[0]))
    name, outfile = args[1], args[2]
    lean_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean')
    if '--lean-dir' in sys.argv: lean_dir = sys.argv[sys.argv.index('--lean-dir') + 1]
    out, (T0, k0, R, al, be) = build(cert)
    for (cl, phs, off) in out:
        assert list(off) == [al * R, al * cl['i'] + be], (cl['i'], off)
    ds, cuts, sts = run_probe(cert, out, lean_dir, name, K)
    ns = 'Family.Cert.%s' % name
    s = 'import FamilyMain\nimport Cert.%s.Init\nnamespace %s\nopen Family\n\n' % (name, ns)
    s += '/-! Steady-round certificate of wall %s (generated by m6/gen/emit_round.py). -/\n\n' % name
    defs, names = chunk_defs(cert, out, ds, cuts, sts)
    s += defs + '\n' + cert_def(cert, out, names) + '\n'
    for i, nm in enumerate(names):
        for k, c in enumerate(nm):
            s += ('theorem ck%d_%d : chunkOk (cert.env %d) (cert.cls %d).j0 %s %s = true := by decide +kernel\n'
                  % (i, k, i, i, 'true' if k == 0 else 'false', c))
    s += '\n'
    for i, nm in enumerate(names):
        t = '(chunksOk_nil _ _ _)'
        for k in range(len(nm) - 1, -1, -1):
            t = '(chunksOk_cons ck%d_%d %s)' % (i, k, t)
        s += 'theorem cks%d : chunksOk (cert.env %d) (cert.cls %d).j0 true (cert.cls %d).chunks = true :=\n  %s\n\n' % (i, i, i, i, t)
    cases = ''.join('    | %d, _ => cks%d\n' % (i, i) for i in range(R))
    s += ('theorem round_ok : check cert = true :=\n'
          '  check_of_parts cert (by decide +kernel) (by decide +kernel) (fun i hi =>\n'
          '    match i, hi with\n%s    | n + %d, hi => absurd hi (Nat.not_lt.2 (Nat.le_add_left _ _)))\n\n' % (cases, R))
    s += ('theorem init_ok : cert.InitOk := by\n'
          '  intro x\n'
          '  have e1 : endShape = (cert.cls (cert.k0 % cert.R)).init := by decide +kernel\n'
          '  have e2 : endCnt = evC (cert.cls (cert.k0 % cert.R)).cn0 (cert.k0 / cert.R) 0 := by decide +kernel\n'
          '  have e3 : endRows = cert.T0 := by decide\n'
          '  have h := initial_run x\n'
          '  rw [e1, e2, e3] at h\n'
          '  exact h\n\n')
    s += 'def certified : Cert := ⟨cert, init_ok⟩\n\n'
    s += ('/-- The wall law of wall %s. -/\n'
          'theorem wall : WallLaw cert := family_wall_law certified round_ok\n\n' % name)
    s += 'end %s\n' % ns
    open(outfile, 'w').write(s)
    print('wrote', outfile, len(s.splitlines()), 'lines; chunks', [len(c) for c in cuts], 'd =', ds)


if __name__ == '__main__':
    main()
