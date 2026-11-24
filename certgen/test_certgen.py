"""Light checks of the certificate generator (about a minute; needs numpy and a C compiler).   python3 -m certgen.test_certgen"""
import tempfile, time

from . import certify, game3, store, walls

XCHECK = ['r10:s1-2-5-6-9_g00112233041520314_p12', 'r10:s3-4-9-10_g00112233041520314_p12',          # N = 12
          'r10:s1-3-5-8_g001122330410213203_p10', 'r10:s1-4-7-8-9-10_g00112233041520310213_p12',
          'r10:s5-6-7-9_g0011223340510213203_p11',
          'A', 'B', 'p7_12:s1-2-3-6-8_g0102211_p0', 'r10:s1-2-5-9_g012345678_p0',
          'p78_rand:s4-5-6-7-8-10_g01000022_p0']                                                   # N = 0


def test_loader_counts():
    a, d = walls.load_m5a(), walls.load_m5d()
    assert (len(a), len(d)) == (32, 30)
    for r in a + d:
        assert r['gper'] and r['S1'] and r['classes'] and len(r['classes']) == r['q']
        assert all(isinstance(x, int) for x in r['gpre'] + r['gper'])
    assert [r for r in d if len(r['gper']) == 11][0]['gper'] == list(range(11))   # n >= 10 from the digits
    assert walls.parse_poly('59.5k^2 + 246.5k + 181')[0] * 2 == 119
    assert walls.parse_poly('89 + 20k') == (0, 20, 89)
    assert sum(1 for r in a if r['gpre']) >= 10


def test_duplicates():
    a = walls.load_m5a()
    g = walls.distinct(a + [dict(a[0], id='copy')])
    assert len(g) == len(a) and g[0][1] == [a[0]['id'], 'copy']
    allr = walls.load_all()
    assert len(walls.distinct(allr)) == len(set(walls.game_key(r) for r in allr))


def _by(tag):
    return [r for r in walls.load_m5a() if r['id'] == tag][0]


def test_rowgen3_vs_full_table():
    n_pre = 0
    for rid in XCHECK:
        r = _by(rid)
        p = len(r['gper'])
        for mult in range(1, 21):          # least multiple of p that is a tail period of the rows
            try:
                bad = game3.crosscheck(r['S1'], r['gpre'], r['gper'], p * mult, M=400, D=700)
                break
            except game3.NotPeriodic:
                continue
        else:
            raise AssertionError('no tail period for ' + rid)
        assert bad == 0, rid
        n_pre += bool(r['gpre'])
    assert n_pre == 5


def test_certificates_readable():
    assert len(store.names()) == 45 and len(store.lean_walls()) == 32
    for i in store.names():
        c = store.load(i)
        assert c['format'] == 'm6-cert-1' and c['wall']['name'] == i, i


def test_certificates_of_A_and_B_found_again():
    for name in 'AB':
        rec = _by(name)
        with tempfile.TemporaryDirectory() as out:
            summ, cert = certify.certify(rec, [name], out_dir=out, log=lambda s: None)
        kept = store.load(name)
        assert summ['status'] == 'closed' and summ['mismatches'] == 0 and summ['law_matches_table']
        for k in ('wall', 'R', 'k0', 'law', 'initial', 'classes'): assert cert[k] == kept[k], (name, k)


if __name__ == '__main__':
    for n, f in sorted(globals().items()):
        if n.startswith('test_') and callable(f):
            t = time.time(); f(); print('PASS', n, '%.1fs' % (time.time() - t), flush=True)
