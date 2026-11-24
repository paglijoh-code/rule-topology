"""Write the round modules of the walls (after certgen.emit_all).  Needs the Lean checker built (`cd lean && lake build
FamilyMain`): the generator asks Lean for the literal states between chunks.

    python3 -m certgen.emit_rounds [--lean-dir DIR] [--no-limits] [--all | ID ...]

Cert/<n>/RoundDefs.lean  chunk and cert definitions        (imports FamilyMain, Cert.<n>.Wall)
Cert/<n>/Ck<nnn>.lean    groups of `theorem ck*`            (import RoundDefs)
Cert/<n>/Round.lean      cks*, round_ok, init_ok, wall      (imports Init and all Ck)
Definitions are `noncomputable def` (only the kernel unfolds them)."""
import json, os, re, subprocess, sys, tempfile

from . import store
from .emit_all import options

HERE = os.path.dirname(os.path.abspath(__file__))
G = 8        # ck theorems per module


def split(n, text, d, limits=True):
    lines = text.split('\n')
    i0 = next(i for i, l in enumerate(lines) if l.startswith('theorem ck'))
    i1 = next(i for i, l in enumerate(lines) if l.startswith('theorem cks'))
    head, cks, tail = lines[:i0], [l for l in lines[i0:i1] if l.startswith('theorem ck')], lines[i1:]
    head = '\n'.join(head)
    head = head.replace('import Cert.%s.Init' % n, 'import Cert.%s.Wall' % n)
    head = re.sub(r'(?m)^def ', 'noncomputable def ', head)
    if limits: head = head.replace('open Family\n', 'open Family\nset_option maxRecDepth 100000\n', 1)
    ns = 'Family.Cert.%s' % n
    open(os.path.join(d, 'RoundDefs.lean'), 'w').write(head.rstrip('\n') + '\n\nend %s\n' % ns)
    # resource limit only, the check is the same: heavy chunks exceed the default
    hb = 'set_option maxHeartbeats 0\n' if limits else ''
    mods = []
    for g in range(0, len(cks), G):
        m = 'Ck%03d' % (g // G)
        mods.append(m)
        open(os.path.join(d, m + '.lean'), 'w').write(
            'import Cert.%s.RoundDefs\nnamespace %s\nopen Family\n%s\n%s\n\nend %s\n' % (n, ns, hb, '\n'.join(cks[g:g + G]), ns))
    imports = ''.join('import Cert.%s.%s\n' % (n, m) for m in mods)
    body = '\n'.join(tail)
    body = re.sub(r'(?m)^def ', 'noncomputable def ', body)
    open(os.path.join(d, 'Round.lean'), 'w').write(
        'import FamilyMain\nimport Cert.%s.Init\nimport Cert.%s.RoundDefs\n%snamespace %s\nopen Family\n\n%s'
        % (n, n, imports, ns, body))
    return len(cks), len(mods)


def one(i, n, lean_dir, limits):
    d = os.path.join(lean_dir, 'Cert', n)
    r = subprocess.run(['lake', 'build', '+Cert.%s.Wall' % n], cwd=lean_dir, capture_output=True, text=True)
    if r.returncode:
        raise SystemExit('%s: %s' % (i, (r.stdout + r.stderr)[-600:]))
    with tempfile.TemporaryDirectory() as tmp:
        cert, rnd = os.path.join(tmp, 'cert.json'), os.path.join(tmp, 'round.lean')
        json.dump(store.load(i), open(cert, 'w'))
        r = subprocess.run([sys.executable, os.path.join(HERE, 'emit_round.py'), cert, n, rnd, '--lean-dir', lean_dir],
                           capture_output=True, text=True)
        if r.returncode:
            raise SystemExit('%s: %s' % (i, (r.stdout + r.stderr)[-600:]))
        return split(n, open(rnd).read(), d, limits)


if __name__ == '__main__':
    o = options(__doc__)
    for i, n in store.select(o.ids, 'all' if o.all else 'lean'):
        print(i, *one(i, n, os.path.abspath(o.lean_dir), not o.no_limits), flush=True)
