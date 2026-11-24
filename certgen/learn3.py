"""Learn the round certificate of a wall from an (interned) symbolic run."""


def factor(seq, lo, hi, maxP=2000):
    """greedy factorisation of seq[lo:hi] into singles and cycles (P, c>=2)."""
    toks = []
    i = lo
    while i < hi:
        best = None
        si = seq[i]
        for P in range(1, min(maxP, (hi - i) // 2) + 1):
            if si != seq[i + P]: continue
            if seq[i:i + P] != seq[i + P:i + 2 * P]: continue
            c = 2
            while i + (c + 1) * P <= hi and seq[i + c * P:i + (c + 1) * P] == seq[i:i + P]: c += 1
            if best is None or c * P > best[0] * best[1]: best = (P, c)
        if best:
            P, c = best
            if i > 0 and seq[i - 1] != seq[i + P - 1]:     # entry pass is not a cycle iteration: P singles
                for q in range(P): toks.append(('s', seq[i + q], 1, i + q))
                i += P; c -= 1
            if c >= 2:
                toks.append(('c', tuple(seq[i:i + P]), c, i)); i += P * c
            else:
                for q in range(P * c): toks.append(('s', seq[i + q], 1, i + q))
                i += P * c
        else:
            toks.append(('s', seq[i], 1, i)); i += 1
    return toks


def sig(toks):
    return tuple((t[0], t[1]) for t in toks)


def affine(vals):
    return all(vals[i] - 2 * vals[i + 1] + vals[i + 2] == 0 for i in range(len(vals) - 2))


def shape_letters(key):
    return sum(len(b) for b in key[0]) + sum(len(y) for y in key[1]) + len(key[2])


def kmax_of(tf, n):
    K = 0
    while tf(K + 1) <= n: K += 1
    return K


def class_ok(run, tf, rounds, R, k0, Kmax):
    """affine-in-j checks for all classes; returns None if fine else a reason"""
    hist = run.hist
    for i in range(R):
        ks = list(range(k0 + ((i - k0) % R), Kmax, R))
        if len(ks) < 4: return 'few samples class %d' % i
        if len(set(hist[tf(k) - 1][0] for k in ks)) != 1: return 'Init shape differs in class %d' % i
        T = len(rounds[ks[0]])
        for ti in range(T):
            if not affine([rounds[k][ti][2] for k in ks]): return 'count not affine class %d token %d' % (i, ti)
            cv = [hist[rounds[k][ti][3]][1] for k in ks]
            for ci in range(len(cv[0])):
                if not affine([c[ci] for c in cv]): return 'counter not affine class %d token %d' % (i, ti)
        cv = [hist[tf(k) - 1][1] for k in ks]
        for ci in range(len(cv[0])):
            if not affine([c[ci] for c in cv]): return 'init counter not affine class %d' % i
        if not affine([tf(k + 1) - tf(k) for k in ks]): return 'gap not affine class %d' % i
    return None


def analyze(run, tf, Rmax=60, rcache=None, minper=4):
    """Look for (R, k0) in the rows computed so far.  Returns dict(closes, ...)."""
    n = run.n
    seq = [h[0] for h in run.hist]
    Kmax = kmax_of(tf, n)
    rcache = {} if rcache is None else rcache
    res = dict(rows=n, rounds_tested=Kmax, closes=False)
    k_first = 0
    while tf(k_first) < 1: k_first += 1
    for k in range(k_first, Kmax):
        if k not in rcache: rcache[k] = factor(seq, tf(k), tf(k + 1))
    rounds = rcache
    why = 'no period found'
    for R in range(1, Rmax + 1):
        if Kmax - R - 1 < k_first: break
        k0 = None
        for k in range(Kmax - R - 1, k_first - 1, -1):
            if sig(rounds[k]) == sig(rounds[k + R]): k0 = k
            else: break
        if k0 is None: continue
        while Kmax - k0 >= minper * R:
            bad = class_ok(run, tf, rounds, R, k0, Kmax)
            if bad is None:
                res.update(closes=True, R=R, k0=k0)
                return res, rounds
            why = 'R=%d k0=%d: %s' % (R, k0, bad)
            k0 += 1
        why = why if why != 'no period found' else 'R=%d: period found too late (k0=%d, rounds %d)' % (R, k0, Kmax)
    res['why'] = why
    return res, rounds


def stats(run, tf, rounds, R, k0):
    """letters / shapes figures (see brief item 5)"""
    keys = run.keys
    shl = [shape_letters(k) for k in keys]
    seq = [h[0] for h in run.hist]
    init_rows = tf(k0)
    out = dict(initial_rows=init_rows, initial_letters=sum(shl[s] for s in seq[:init_rows]))
    steady = set()
    for k in range(k0, k0 + R):
        for t in rounds[k]:
            for s in ((t[1],) if t[0] == 's' else t[1]):
                steady.add(s)
    out['steady_shapes'] = len(steady)
    out['steady_letters'] = sum(shl[s] for s in steady)
    out['max_blocks'] = max(len(keys[s][1]) for s in steady)
    out['max_boundary'] = max(max(len(b) for b in keys[s][0]) for s in steady)
    return out
