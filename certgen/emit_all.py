"""Write the initial-run modules of the walls: LEAN_DIR/Cert/W<id>/{Wall,I00..,Init}.lean.

    python3 -m certgen.emit_all [--lean-dir DIR] [--no-limits] [--all | ID ...]
"""
import argparse, os, re

from . import emit_lean3, store

ROOT = store.ROOT


def options(doc):
    ap = argparse.ArgumentParser(description=doc)
    ap.add_argument('ids', nargs='*', help='wall ids (default: the 32 walls with status LEAN)')
    ap.add_argument('--all', action='store_true', help='all 45 generated walls')
    ap.add_argument('--lean-dir', default=os.path.join(ROOT, 'lean'), help='directory that holds Cert/ (default: lean)')
    ap.add_argument('--no-limits', action='store_true',
                    help='leave out the set_option resource-limit lines (as in the reference files)')
    return ap.parse_args()


if __name__ == '__main__':
    o = options(__doc__)
    for i, n in store.select(o.ids, 'all' if o.all else 'lean'):
        d = os.path.join(o.lean_dir, 'Cert', n)
        k = emit_lean3.emit_initial(store.load(i), n, d, limits=not o.no_limits)
        # data defs are only ever unfolded by the kernel (`decide +kernel`): skip code generation
        for f in os.listdir(d):
            if f == 'Init.lean' or re.fullmatch(r'I\d+\.lean', f):
                t = open(os.path.join(d, f)).read()
                open(os.path.join(d, f), 'w').write(re.sub(r'(?m)^def ', 'noncomputable def ', t))
        print(i, n, k, flush=True)
