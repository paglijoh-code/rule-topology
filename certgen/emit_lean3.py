"""Emit the Lean initial-run certificate of a wall.

    python -m certgen.emit_lean3 initial CERT.json NAME OUTDIR

writes OUTDIR/Wall.lean, OUTDIR/I00.lean ... and OUTDIR/Init.lean (module prefix Cert.<NAME>).
Each I<nn> module is an independent `decide +kernel` check of one segment of K rows between two
literal checkpoints; Init chains them with `seg_next` and `start_sound`.
"""
import sys, os, json


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


def lst(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def shp(b, y, z):
    blocks = ', '.join('(%s, %s)' % (lst(y[i]), lst(b[i + 1])) for i in range(len(y)))
    return '⟨%s, [%s], %s⟩' % (lst(b[0]), blocks, lst(z))


def start_moves(cert):
    """initial normalisation of Sigma_0: the `start` moves recorded in the certificate (all tpull); the
    shape after them is x0 = z^len(start), no blocks (gpre-aware: nothing is rebuilt from the wall tables)."""
    ms = cert['initial']['start']
    assert all(m[0] == 'tpull' for m in ms)
    z = [0] * len(cert['wall']['gper'])
    return ms, [z * len(ms)], [], z, []


def emit_initial(cert, name, outdir, limits=True):
    os.makedirs(outdir, exist_ok=True)
    w = cert['wall']
    steps = cert['initial']['steps']
    cps = cert['initial']['checkpoints']
    ns = 'Family.Cert.%s' % name
    ms, b0, y0, z0, n0 = start_moves(cert)
    with open(os.path.join(outdir, 'Wall.lean'), 'w') as f:
        f.write('import FamilyFast\nnamespace %s\n' % ns)
        f.write('def S1 : List Nat := %s\ndef gpre : List Nat := %s\ndef gper : List Nat := %s\n'
                % (lst(w['S1']), lst(w['gpre']), lst(w['gper'])))
        f.write('def start : List Family.Move := %s\n' % ('[' + ', '.join('.tailOut' for _ in ms) + ']'))
        f.write('theorem hS : ∀ s ∈ S1, 0 < s := by decide\n')
        f.write('theorem hp : 0 < gper.length := by decide\nend %s\n' % ns)
    pts = [(0, shp(b0, y0, z0), lst(n0))]
    for c in cps:
        pts.append((c['rows'], shp(c['b'], c['y'], c['z']), lst(c['cnt'])))
    nseg = len(pts) - 1
    for i in range(nseg):
        a, b = pts[i][0], pts[i + 1][0]
        with open(os.path.join(outdir, 'I%02d.lean' % i), 'w') as f:
            f.write('import Cert.%s.Wall\nnamespace %s.I%02d\nopen Family\n' % (name, ns, i))
            f.write('def rows : List (List Move) := [\n%s]\n' % ',\n'.join(mvs(s) for s in steps[a:b]))
            f.write('def s0 : Shape := %s\ndef n0 : List Nat := %s\n' % (pts[i][1], pts[i][2]))
            f.write('def s1 : Shape := %s\ndef n1 : List Nat := %s\n' % (pts[i + 1][1], pts[i + 1][2]))
            f.write('theorem ok : segCheckF S1 gpre gper %d s0 n0 rows s1 n1 = true := by decide +kernel\n' % a)
            f.write('theorem len : %d + rows.length = %d := by decide\nend %s.I%02d\n' % (a, b, ns, i))
    with open(os.path.join(outdir, 'Init.lean'), 'w') as f:
        f.write('import Cert.%s.Wall\n' % name)
        for i in range(nseg):
            f.write('import Cert.%s.I%02d\n' % (name, i))
        f.write('namespace %s\nopen Family\n\n' % ns)
        f.write('def endRows : Nat := %d\ndef endShape : Shape := I%02d.s1\ndef endCnt : List Nat := I%02d.n1\n\n'
                % (pts[-1][0], nseg - 1, nseg - 1))
        f.write('theorem start_eq : applyMoves (sigma0 gper.length) [] start = some (I00.s0, I00.n0) := by\n'
                '  decide +kernel\n\n')
        # Long walls chain >1000 `have`s in one declaration; elaboration heartbeats
        # accumulate (r10:s1-2-7-9-10 timed out at 200000). Elaboration budget only.
        # `set_option ... in` must precede the doc comment, not sit between it and the theorem.
        # 1000000 still timed out on s2-4-10-12 (kernel check of initial_run): no limit.
        if limits: f.write('set_option maxHeartbeats 0 in\n')
        f.write('/-- The concrete initial run: the stack after `endRows` rows is `decode endShape endCnt`. -/\n')
        f.write('theorem initial_run : ∀ x, decode endShape endCnt x = St S1 gpre gper endRows x := by\n')
        f.write('  have d := start_sound S1 gpre gper start_eq\n')
        for i in range(nseg):
            f.write('  have d%d := seg_next S1 gpre gper hS hp I%02d.ok I%02d.len\n'
                    '    (by decide +kernel) d\n' % (i, i, i) if i == 0 else
                    '  have d%d := seg_next S1 gpre gper hS hp I%02d.ok I%02d.len\n'
                    '    (by decide +kernel) d%d\n' % (i, i, i, i - 1))
        f.write('  exact d%d\n\nend %s\n' % (nseg - 1, ns))
    return nseg


if __name__ == '__main__':
    if sys.argv[1] == 'initial':
        cert = json.load(open(sys.argv[2]))
        print(emit_initial(cert, sys.argv[3], sys.argv[4]), 'segments')
