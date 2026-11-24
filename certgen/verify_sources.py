"""Compare generated Lean sources with the recorded digests of the files that were kept (certificates/reference.json).

    python3 -m certgen.verify_sources LEAN_DIR [--initial] [ID ...]

`raw` compares the files byte by byte; `text` ignores lines that only set a resource limit (`set_option maxHeartbeats`,
`set_option maxRecDepth`), which do not change what is checked.  --initial compares only Wall, I<nn> and Init."""
import argparse, hashlib, json, os, re, sys

from . import store

LIMIT = re.compile(rb'(?m)^set_option max(Heartbeats|RecDepth) .*\n')


def is_initial(f):
    return f in ('Wall.lean', 'Init.lean') or re.fullmatch(r'I\d+\.lean', f) is not None


def digest(d, initial=False):
    """number of files and the digests (raw, text) of the .lean files of one wall"""
    raw, text = hashlib.sha256(), hashlib.sha256()
    n = 0
    for f in sorted(os.listdir(d)):
        if not f.endswith('.lean') or initial and not is_initial(f): continue
        b = open(os.path.join(d, f), 'rb').read()
        raw.update(('%s %s\n' % (f, hashlib.sha256(b).hexdigest())).encode())
        text.update(('%s %s\n' % (f, hashlib.sha256(LIMIT.sub(b'', b)).hexdigest())).encode())
        n += 1
    return dict(files=n, raw=raw.hexdigest(), text=text.hexdigest())


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('lean_dir'); ap.add_argument('--initial', action='store_true'); ap.add_argument('ids', nargs='*')
    o = ap.parse_args()
    ref = json.load(open(os.path.join(store.CERTS, 'reference.json')))
    part = 'initial' if o.initial else 'all'
    bad = raw = 0
    ids = o.ids or list(ref)
    for i in ids:
        r = ref[i]
        d = os.path.join(o.lean_dir, 'Cert', r['name'])
        got = digest(d, o.initial) if os.path.isdir(d) else None
        ok = got is not None and (got['files'], got['text']) == (r[part]['files'], r[part]['text'])
        same = ok and got['raw'] == r[part]['raw']
        bad += not ok; raw += same
        print('%-4s %s %d files%s' % ('ok' if ok else 'BAD', i, r[part]['files'], '' if same else ' (not byte-identical)'))
    print('%d of %d walls agree, %d of them byte-identical' % (len(ids) - bad, len(ids), raw))
    sys.exit(bad > 0)
