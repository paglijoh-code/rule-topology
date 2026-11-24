#!/usr/bin/env python3
"""exponent.py : chaos/stripe boundary of a start-mode table and its growth exponent.

Table T[a][b] (b >= a), rows r_a(d) = T[a][a+d]. For each row the eventual period p (<= PMAX,
smallest period of the last TAIL cells) and pre(a) = first d from which the row is p-periodic
to the end of the row (d < N - a). Boundary M(a) = running max of pre(a)  (as census_10/fit3 'pre').
Rounds (bounces): records of M clustered with gaps <= GAP rows (census_10/fit3.rounds); T_j is the
first row of round j, L_j the level it lifts M to.

Exponent estimates (a = row):
  slopes     : dyadic log-log slopes of M(a) over windows [a, 2a]  (raw, biased by an offset)
  fit        : M(a) = m0 + c a^alpha (3 parameters, least squares over a >= a_lo), with alpha
               range from refitting on the windows a >= a_lo, 2 a_lo, 4 a_lo
  bounce     : T_j ~ j^gamma over dyadic windows in j; alpha_b = 1/gamma  (each bounce lifts M by
               ~const, so j ~ M). sqrt law: T_j quadratic in j, gamma = 2, alpha_b = 1/2.
"""
import numpy as np


def row_pre(T, amax=None, dmax=None, pmax=100, tail=400):  # pilot uses pmax=400, tail=1200
    n1 = T.shape[0]
    amax = amax if amax is not None else n1 // 2
    pre = np.zeros(amax, dtype=np.int64)
    per = np.zeros(amax, dtype=np.int64)
    bad = 0
    for a in range(amax):
        x = T[a, a:]
        if dmax is not None:
            x = x[:dmax]
        L = len(x)
        t = min(tail, L // 2)
        w = x[L - t:]
        p = 0
        for q in range(1, pmax + 1):
            if t >= 3 * q and (w[q:] == w[:-q]).all():
                p = q
                break
        if p == 0:
            pre[a] = 0           # no short eventual period: row excluded from M (counted in bad; >5% -> kind noperiod)
            bad += 1
            continue
        mis = np.nonzero(x[:-p] != x[p:])[0]
        pre[a] = mis[-1] + 1 if len(mis) else 0
        per[a] = p
    return pre, per, bad


def rounds(M, gap=40):
    idx = np.nonzero(np.diff(M))[0] + 1
    if len(idx) == 0:
        return np.array([], int), np.array([], int)
    cl = [[idx[0]]]
    for i, g in zip(idx[1:], np.diff(idx)):
        (cl.append([i]) if g > gap else cl[-1].append(i))
    return np.array([c[0] for c in cl]), np.array([M[c[-1]] for c in cl])


def dyadic_slopes(x, y, x_lo):
    """log-log slope of y between x and 2x for x = x_lo, 2 x_lo, ... (x up to max/2)."""
    out = []
    x0 = x_lo
    while 2 * x0 <= x[-1]:
        i0 = np.searchsorted(x, x0)
        i1 = np.searchsorted(x, 2 * x0)
        y0, y1 = y[min(i0, len(y) - 1)], y[min(i1, len(y) - 1)]
        if y0 > 0 and y1 > 0:
            out.append((x0, float(np.log(y1 / y0) / np.log(2))))
        x0 *= 2
    return out


def _fit_alpha(a, M, a_lo):
    """least squares M = m0 + c a^alpha, a >= a_lo; scan alpha, solve m0,c linearly. returns (alpha, resid)"""
    sel = a >= a_lo
    aa, MM = a[sel].astype(float), M[sel].astype(float)
    if len(aa) < 20 or MM.max() == MM.min():
        return None
    best = None
    for al in np.arange(0.05, 1.5001, 0.005):
        X = np.stack([np.ones_like(aa), aa ** al], 1)
        coef, *_ = np.linalg.lstsq(X, MM, rcond=None)
        with np.errstate(all='ignore'):
            r = ((X @ coef - MM) ** 2).sum()
        if best is None or r < best[1]:
            best = (al, r, coef)
    return best


def bounce_fit(T, skip=3):
    """Fit round times T_j = t0 + t1 j + c j^gamma (j counted from the skip-th round), scan gamma in
    [1, 6]; returns 1/gamma or None (fewer than 8 rounds). The free linear term absorbs the early
    offset of walls like 7k^2+49k+52. On synthetic wall-like boundaries it reads about 0.50 for a
    true 1/2, 0.37-0.39 for 1/3 and 0.30-0.32 for 1/4 (biased up: it is a separator, not an
    unbiased estimate)."""
    if len(T) < 8:
        return None
    t = np.asarray(T[skip:], float)
    x = np.arange(1, len(t) + 1, dtype=float)
    best = None
    for g in np.arange(1.0, 6.0001, 0.05):
        X = np.stack([np.ones_like(x), x, x ** g], 1)
        coef, *_ = np.linalg.lstsq(X, t, rcond=None)
        r = ((X @ coef - t) ** 2).sum()
        if best is None or r < best[1]:
            best = (g, r)
    return round(float(1.0 / best[0]), 3)


def fit_exponent(M, a_lo=None):
    n = len(M)
    a = np.arange(n)
    a_lo = a_lo or max(n // 16, 16)
    res = {"n_rows": n, "M_end": int(M[-1])}
    if M[-1] - M[n // 4] <= 2:
        sat = int(np.nonzero(M >= M[-1])[0][0])
        # "bounded" means M is exactly flat from row n/4 on. A rise of 1..2 after n/4 is "slow"
        # (log-like growth or a late saturation); it must not be reported as bounded.
        kind = "none" if M[-1] == 0 else ("bounded" if M[-1] == M[n // 4] else "slow")
        res.update(kind=kind, alpha=0.0, lo=0.0, hi=0.0, sat_row=sat,
                   note="no growing boundary (M flat after row n/4)" if kind != "slow" else
                   "M still rising after row n/4 by 1..2: slow (log-like?) growth or late saturation")
        return res
    fits = []
    for lo in (a_lo, 2 * a_lo, 4 * a_lo):
        f = _fit_alpha(a, M, lo)
        if f:
            fits.append(f[0])
    sl = dyadic_slopes(a, M, a_lo)
    res["slopes"] = [(int(x), round(s, 3)) for x, s in sl]
    res["fit_alphas"] = [round(float(f), 3) for f in fits]
    # bounce (round) estimate from second differences of the round times (kills the linear offset)
    T, L = rounds(M)
    res["n_rounds"] = int(len(T))
    res["rounds_T"] = [int(t) for t in T[:80]]
    res["rounds_L"] = [int(l) for l in L[:80]]
    ab = []
    if len(T) >= 12:
        d2 = np.diff(T.astype(float), 2)
        n2 = len(d2)
        res["T_rounds_head"] = [int(t) for t in T[:6]]
        gs = []
        j0 = 2
        while 4 * j0 <= n2:
            if 8 * j0 > n2:          # only the largest windows (small j carry the pre-asymptotic bias)
                m1 = d2[j0:2 * j0].mean()
                m2 = d2[2 * j0:4 * j0].mean()
                if m1 > 0 and m2 > 0:
                    gs.append(2 + float(np.log2(m2 / m1)))
            j0 += 1 if j0 < 8 else j0 // 4
        res["bounce_gamma"] = [round(g, 3) for g in gs]
        ab = [1.0 / g for g in gs if g > 0.5]
        res["alpha_bounce"] = [round(x, 3) for x in ab]
    bf = bounce_fit(T)
    res["alpha_bfit"] = bf
    vals = list(fits) + ab + ([bf] if bf is not None else [])
    cen = float(np.median(vals)) if vals else float("nan")
    spread = max(vals) - min(vals) if vals else float("nan")
    res.update(alpha=round(cen, 3), lo=round(min(vals), 3), hi=round(float(max(vals)), 3), kind="growing")
    res["confidence"] = ("high" if len(T) >= 20 and spread <= 0.1 else
                         "medium" if len(T) >= 12 and spread <= 0.2 else "low")
    res["alpha_fit"] = round(float(np.median(fits)), 3) if fits else None
    # straight boundary: M = m0 + c a within 4% of M_end (+6) over a >= n/16, and the power fit agrees (>= 0.85).
    # Reported as kind "linear" with alpha 1; without this a continuously climbing M (one merged round) fits junk.
    aa, MM = a[n // 16:].astype(float), M[n // 16:].astype(float)
    c1, c0 = np.polyfit(aa, MM, 1)
    if c1 > 0 and np.abs(MM - (c0 + c1 * aa)).max() <= 0.04 * M[-1] + 6 and res["alpha"] >= 0.85:
        res.update(kind="linear", alpha=1.0, lo=1.0, hi=1.0, slope=round(float(c1), 3))
    return res


def boundary_of_table(T, amax=None, **kw):
    pre, per, bad = row_pre(T, amax=amax, **kw)
    M = np.maximum.accumulate(pre)
    return M, per, bad


def analyse(T, amax=None, **kw):
    M, per, bad = boundary_of_table(T, amax, **kw)
    r = fit_exponent(M)
    if bad > 0.05 * len(M):
        r["kind"] = "noperiod"   # many rows have no short eventual period: the fit is not meaningful
        r["note"] = f"{bad}/{len(M)} rows with no period <= pmax in the tail"
    r["bad_rows"] = int(bad)
    r["max_period"] = int(per.max()) if len(per) else 0
    return r, M
