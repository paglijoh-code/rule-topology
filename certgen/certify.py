"""Certify one distinct game: parameters, symbolic run, closure, brute-force check, certificate + summary line.

    python3 -m certgen.certify ID [--out DIR]          (from the repository root)
"""
import json, os, sys, time
from fractions import Fraction
from math import gcd

import numpy as np

from . import walls, game3, stack3, run3, learn3, emit3, shape3

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'out')

CF = 2
STAGES = [16, 24, 36, 54, 80, 120, 180, 270, 400, 600]
ROWCAP = 1_200_000
LEAN_MS_PER_LETTER = 0.55          # mid of A (0.45) and B (0.68)
SPIKE_TF = {   # the spike's round starts for walls A and B (their initial runs are certified with them)
    ((1, 2, 5, 6), (), (0, 1, 2, 3, 4)): lambda k: 7 * k * k + 35 * k + 13,
    ((1, 2, 3, 4, 7, 8), (), (0, 1, 2, 3, 2, 4)): lambda k: 18 * k * k + 258 * k + 859,
}


class Refused(Exception):
    pass


class Timeout(Exception):
    pass


def make_tf(rec, off=0):
    """round k starts at class-0 record row t_k + off (the table's index k)"""
    key = walls.game_key(rec)
    if key in SPIKE_TF:
        base = SPIKE_TF[key]
        return (lambda k: base(k) + off), True
    a2, a1, a0 = rec['classes'][0]['t']
    A2, A1, A0 = int(2 * a2), int(2 * a1), int(2 * a0)
    assert A2 == 2 * a2 and A1 == 2 * a1 and A0 == 2 * a0
    for k in range(3): assert (A2 * k * k + A1 * k + A0) % 2 == 0

    def tf(k):
        return (A2 * k * k + A1 * k + A0) // 2 + off
    return tf, False


def table_relation(rec, tf):
    """(shift, offset) with tf(k) = t_{k+shift} + offset for the table's class-0 t_k, or None"""
    a2, a1, a0 = rec['classes'][0]['t']
    t0 = lambda k: a2 * k * k + a1 * k + a0
    for s in [0, -1, 1, -2, 2, -3, 3, -4, 4, -5, 5]:
        off = tf(0) - t0(s)
        if all(tf(k) == t0(k + s) + off for k in range(60)):
            return s, int(off)
    return None


def wtab(rec, k):
    w1, w0 = rec['classes'][0]['w']
    return int(w1 * k + w0)


def sample_params(rec, tf, T_max_mult=24):
    """tail period T (multiple of p), row period pi, bulk letter period L0 from a sample table"""
    S1, gpre, gper = rec['S1'], rec['gpre'], rec['gper']
    N, p, m = len(gpre), len(gper), max(S1)
    K1 = 3
    while tf(K1) < 20000 and K1 < 400: K1 += 1
    while K1 > 3 and tf(K1) > 90000: K1 -= 1
    NS = tf(K1) + 1
    T = None
    for mult in range(1, T_max_mult + 1):
        T_ = p * mult
        D = wtab(rec, K1 + 3) + 8 * T_ + 600
        try:
            tab, pre = game3.rows_ring(S1, gpre, gper, NS, D, T_, T_, max(0, NS - 3000), 0, 0)
        except game3.NotPeriodic:
            continue
        T = T_
        break
    if T is None:
        raise Refused('no tail period T <= %d found (rows not periodic)' % (p * T_max_mult))
    # least divisor pi of T with every one of the last ~3000 rows periodic on its last 3T cells
    pi = T
    for d in sorted(x for x in range(1, T + 1) if T % x == 0):
        if all((tab[a, slice(D - 3 * T, D - d)] == tab[a, slice(D - 3 * T + d, D)]).all() for a in tab.rows):
            pi = d; break
    W = stack3.Wall('s', S1, gpre, gper, T)
    mean = {}
    rowsel = [NS - 1 - 37 * i for i in range(5)]
    arrs = []
    for a in rowsel:
        let = np.array(stack3.letters_of(W, tab, a), dtype=np.int64)
        e = len(stack3.from_rows(W, tab, a)[0])
        arrs.append((let, e))
    cand = list(range(p, min(1500, min(e for _, e in arrs) // 3) + 1, p))
    for L in cand:
        mean[L] = float(np.mean([(let[:e - L] == let[L:e]).mean() for let, e in arrs]))
    if not mean:
        raise Refused('stack too short to measure the bulk period (e=%d)' % min(e for _, e in arrs))
    mx = max(mean.values())
    L0 = min(L for L in cand if mean[L] >= 0.92 * mx)
    return dict(T=T, pi=pi, L0=L0, bulk_score=round(mean[L0], 3), NS=NS)


def verify(run, W, rec, NA, pi, tf, Kmax, verbose=False):
    """brute-force table for rows < NA; decode check (every row < 3000, every 53rd after); pre array"""
    S1, gpre, gper = rec['S1'], rec['gpre'], rec['gper']
    K = Kmax
    D = int(max(wtab(rec, K + 3), wtab(rec, 0)) * 1.15) + 8 * W.T + 700 + W.m
    last = None
    for attempt in range(4):
        try:
            tab, pre = game3.rows_ring(S1, gpre, gper, NA, D, W.T, pi, NA + 1, 3000, 53)
            bad = 0
            for n in range(NA):
                if not (n < 3000 or n % 53 == 0): continue
                pre_, z_ = stack3.from_rows(W, tab, n)
                if len(pre_) + 4 * len(z_) + W.m + 8 * W.T > D - W.m:
                    raise AssertionError('D too small for row %d' % n)
                sh = run.shape_at(n)
                Kd = max(len(pre_), sh.finite_len()) + 3 * len(z_) * len(sh.z)
                if shape3.decode(sh, Kd) != stack3.decode(pre_, z_, Kd):
                    bad += 1
            return bad, pre, D
        except (game3.NotPeriodic, AssertionError) as e:
            last = e
            D = int(D * 1.5)
    raise Refused('brute force table unusable (%s)' % last)


def law_of(pre, tf, Kmax, k0, p):
    """pre(t_k) = w0 + delta k, |pre(a) - w_k| <= c on round k (rows with pre(a) > 0)"""
    def try_w(wk):
        d = wk[k0 + 1] - wk[k0]
        if all(wk[k + 1] - wk[k] == d for k in range(k0, Kmax - 1)):
            return d
        return None
    wk = [int(pre[tf(k)]) for k in range(Kmax)]
    d = try_w(wk)
    mode = 'row'
    if d is None:      # round start row happens to have pre 0 on some rounds: take the window maximum
        wk = [int(max(pre[tf(k):tf(k) + 2 * p])) for k in range(Kmax)]
        d = try_w(wk); mode = 'window'
    if d is None:
        return None
    c = max(abs(int(pre[a]) - wk[k]) for k in range(k0, Kmax) for a in range(tf(k), tf(k + 1)) if pre[a] > 0)
    # affine from k0 on: express as w0 + delta*k (valid for k >= k0)
    return dict(pi=None, w0=wk[k0] - d * k0, delta=d, c=c, mode=mode, w_of_k=wk[:8])


def certify(rec, ids, out_dir=OUT, deadline_s=1680, log=lambda s: print(s, flush=True)):
    t_start = time.time()
    S1, gpre, gper = rec['S1'], rec['gpre'], rec['gper']
    N, p, m = len(gpre), len(gper), max(S1)
    summ = dict(id=rec['id'], source=rec['source'], dup_ids=[i for i in ids if i != rec['id']], status='refused',
                reason='', N=N, p=p, m=m, S1=S1, q=rec['q'])
    safe = walls.safe_id(rec['id'])

    def left():
        return deadline_s - (time.time() - t_start)

    try:
        tf0, spike = make_tf(rec, 0)
        sp = sample_params(rec, tf0)
        summ.update(T=sp['T'], pi=sp['pi'], L0=sp['L0'], bulk_score=sp['bulk_score'])
        log('%s: T=%d pi=%d L0=%d (score %.2f)' % (rec['id'], sp['T'], sp['pi'], sp['L0'], sp['bulk_score']))
        W = stack3.Wall(rec['id'], S1, gpre, gper, sp['T'])
        M0 = max(N, m) + 2
        L0 = sp['L0']
        grid = []
        for L in (L0, 2 * L0, 3 * L0):
            for M in (M0, M0 + 6):
                grid.append((L, M))
        reasons = []
        closed = None
        for (L, M) in grid:
            run = run3.Run(W, L, M, CF)
            rcache = {}
            why = None
            for K in STAGES:
                rows = tf0(K) + 3 * p
                if rows > ROWCAP:
                    why = 'row cap %d reached at %d rounds' % (ROWCAP, K); break
                if left() < 0: raise Timeout('internal deadline in stage K=%d (L=%d, M=%d)' % (K, L, M))
                run.advance(rows)
                if run.failed:
                    why = 'sstep failed at row %d: %s' % run.failed; break
                offs = [0]
                if rows >= 25000:
                    offs += [s * o for o in range(1, 3 * p + 1) for s in (1, -1)]
                found = None
                t_off = time.time()
                for off in offs:
                    tf, _ = make_tf(rec, off)
                    if off != 0 and tf(0) < 1: continue
                    res, rounds = learn3.analyze(run, tf, rcache=rcache if off == 0 else None)
                    if res['closes']:
                        found = (off, tf, res, rounds); break
                    if off != 0 and time.time() - t_off > 240: break
                    if left() < 0: raise Timeout('internal deadline in offset sweep (L=%d, M=%d)' % (L, M))
                log('  L=%d M=%d K=%d rows=%d shapes=%d: %s' % (L, M, K, run.n, len(run.keys),
                    'closed R=%d k0=%d off=%d' % (found[2]['R'], found[2]['k0'], found[0]) if found else res.get('why')))
                if found:
                    off, tf, res, rounds = found
                    R, k0, Kmax = res['R'], res['k0'], res['rounds_tested']
                    NA = run.n
                    bad, pre, D = verify(run, W, rec, NA, sp['pi'], tf, Kmax)
                    log('  verified rows %d: mismatches %d (D=%d)' % (NA, bad, D))
                    if bad:
                        why = 'decode mismatches %d vs brute force' % bad; break
                    closed = dict(L=L, M=M, off=off, tf=tf, res=res, rounds=rounds, run=run, bad=bad, pre=pre, D=D,
                                  Kmax=Kmax, NA=NA)
                    break
                rcache_last = res.get('why')
                if K == STAGES[-1]: why = 'no closure up to %d rounds (%s)' % (K, res.get('why'))
            if closed: break
            reasons.append('L=%d M=%d: %s' % (L, M, why or rcache_last))
            if why and why.startswith('sstep failed') or True:
                log('  grid entry L=%d M=%d rejected: %s' % (L, M, reasons[-1]))
        if not closed:
            summ.update(status='refused', reason='; '.join(reasons))
            return summ, None
        run, tf, res, rounds = closed['run'], closed['tf'], closed['res'], closed['rounds']
        R, k0, Kmax = res['R'], res['k0'], closed['Kmax']
        st = learn3.stats(run, tf, rounds, R, k0)
        law = law_of(closed['pre'], tf, Kmax, k0, p)
        rel = table_relation(rec, tf)
        gaps = [tf(k + 1) - tf(k) for k in range(Kmax)]
        lawd = dict(pi=sp['pi'], w0=None, delta=None, alpha=gaps[1] - gaps[0], beta=gaps[0], c=None)
        if law:
            lawd.update(w0=law['w0'], delta=law['delta'], c=law['c'])
        a2 = rec['classes'][0]['t'][0]
        match = bool(law) and rel is not None and law['delta'] == rec['Delta'] and lawd['alpha'] == 2 * a2
        params = dict(L=closed['L'], M=closed['M'], cf=CF, T=sp['T'], D=closed['D'], offset=closed['off'],
                      table_shift=rel[0] if rel else None, table_offset=rel[1] if rel else None,
                      spike_tfun=spike, rows_run=run.n)
        wall_meta = dict(name=rec['id'])
        cert = emit3.build_cert(run, tf, rounds, R, k0, Kmax, wall_meta, W, params,
                                dict(pi=lawd['pi'], w0=lawd['w0'], delta=lawd['delta'], c=lawd['c'],
                                     w_of_k=(law or {}).get('w_of_k')))
        os.makedirs(os.path.join(out_dir, 'certs'), exist_ok=True)
        cpath = os.path.join(out_dir, 'certs', safe + '.json')
        json.dump(cert, open(cpath + '.tmp', 'w'))
        os.replace(cpath + '.tmp', cpath)
        summ.update(status='closed', reason='', L=closed['L'], M=closed['M'], D=closed['D'], T=sp['T'],
                    offset=closed['off'], table_shift=params['table_shift'], table_offset=params['table_offset'],
                    R=R, k0=k0, initial_rows=st['initial_rows'], initial_letters=st['initial_letters'],
                    steady_shapes=st['steady_shapes'], steady_letters=st['steady_letters'],
                    max_blocks=st['max_blocks'], max_boundary=st['max_boundary'],
                    mismatches=closed['bad'], rows_run=run.n, rounds=Kmax,
                    law=lawd, law_ok=bool(law), law_matches_table=match,
                    lean_cpu_s=round(st['initial_letters'] * LEAN_MS_PER_LETTER / 1000, 1), cert=os.path.relpath(cpath, out_dir))
        return summ, cert
    except Refused as e:
        summ.update(status='refused', reason=str(e))
        return summ, None
    except Timeout as e:
        summ.update(status='timeout', reason=str(e))
        return summ, None
    except Exception as e:      # noqa
        import traceback
        summ.update(status='error', reason='%s: %s' % (type(e).__name__, e), trace=traceback.format_exc()[-1500:])
        return summ, None
    finally:
        summ['seconds'] = round(time.time() - t_start, 1)


def by_id():
    out = {}
    for rec, ids in walls.distinct(walls.load_all()):
        for i in ids: out[i] = (rec, ids)
    return out


def main(argv):
    out_dir = OUT
    if '--out' in argv:
        out_dir = argv[argv.index('--out') + 1]
    wid = argv[1]
    rec, ids = by_id()[wid]
    summ, _ = certify(rec, ids, out_dir)
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, 'result_%s.json' % walls.safe_id(rec['id'])), 'w') as f:
        json.dump(summ, f)
    print(json.dumps({k: v for k, v in summ.items() if k != 'trace'}))
    return 0 if summ['status'] == 'closed' else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
