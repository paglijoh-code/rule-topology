"""Wall loader: experiments/census_10/walls_exact.jsonl (32) + experiments/prediction/results/census.jsonl sqrt records (30) -> normalised records.

Record: {id, source, S1, gpre, gper, q, classes: [{t: (a2, a1, a0) Fractions, w: (w1, w0), k_range}]}
(t_k = a2 k^2 + a1 k + a0 = record row of class k, w_k = w1 k + w0 = wall level).
"""
import gzip, json, os, re
from fractions import Fraction

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))


def parse_poly(s):
    """'14k^2 + 98k + 104' / '89 + 20k' / '59.5k^2 + 246.5k + 181' -> (a2, a1, a0) Fractions"""
    c = {0: Fraction(0), 1: Fraction(0), 2: Fraction(0)}
    for term in s.replace(' ', '').replace('-', '+-').split('+'):
        if not term: continue
        mo = re.fullmatch(r'(-?[0-9.]*)(?:k(?:\^([0-9]))?)?', term)
        assert mo, term
        coef, e = mo.group(1), mo.group(2)
        has_k = 'k' in term
        deg = (int(e) if e else 1) if has_k else 0
        c[deg] += Fraction(coef) if coef not in ('', '-') else Fraction(-1 if coef == '-' else 1)
    return (c[2], c[1], c[0])


def parse_g(digits):
    """'012345678910' -> n (the consecutive integers 0..n-1 concatenated)"""
    k, pos = 0, 0
    while pos < len(digits):
        sk = str(k)
        assert digits.startswith(sk, pos), digits
        pos += len(sk); k += 1
    return k


def load_m5a(path=None):
    path = path or os.path.join(ROOT, 'experiments', 'census_10', 'walls_exact.jsonl')
    out = []
    for line in open(path):
        r = json.loads(line)
        g = r['g']
        pat = g['pattern']
        N, p = g['pre'], g['per']
        assert len(pat) == N + p
        cls = []
        for c in r['classes']:
            cls.append(dict(t=(Fraction(c['t_k']['a2']), Fraction(c['t_k']['a1']), Fraction(c['t_k']['a0'])),
                            w=(Fraction(c['w_k']['a1']), Fraction(c['w_k']['a0'])), k_range=tuple(c['k_range'])))
        out.append(dict(id=r['tag'], source='census_10', S1=list(r['S1']), gpre=list(pat[:N]), gper=list(pat[N:]),
                        q=r['q'], Delta=r['Delta'], classes=cls))
    return out


def load_m5d(path=None):
    path = path or os.path.join(ROOT, 'experiments', 'prediction', 'results', 'census.jsonl')
    out = []
    for line in open(path):
        r = json.loads(line)
        if r.get('status') != 'ok' or r.get('fit', {}).get('kind') != 'sqrt': continue
        mo = re.fullmatch(r's([0-9-]+)_g([0-9]+)_p0', r['name'])
        assert mo, r['name']
        S1 = [int(x) for x in mo.group(1).split('-')]
        n = parse_g(mo.group(2))
        f = r['fit']
        cls = []
        for c in f['classes']:
            w = parse_poly(c['w_k'])
            cls.append(dict(t=parse_poly(c['t_k']), w=(w[1], w[2]), k_range=(0, c['k_checked'])))
        out.append(dict(id=r['name'], source='prediction', S1=S1, gpre=[], gper=list(range(n)), q=f['q'],
                        Delta=f['Delta'], classes=cls))
    return out


def load_all():
    return load_m5a() + load_m5d()


def game_key(r):
    return (tuple(r['S1']), tuple(r['gpre']), tuple(r['gper']))


def distinct(recs):
    """group records by game: list of (representative record, [all ids]) in first-seen order"""
    groups = {}
    for r in recs:
        groups.setdefault(game_key(r), []).append(r)
    return [(g[0], [x['id'] for x in g]) for g in groups.values()]


def safe_id(i):
    return re.sub(r'[^A-Za-z0-9_.-]', '_', i)


def ordered(recs):
    """the distinct games, cheapest first is decided by the driver; here just a stable list"""
    return distinct(recs)
