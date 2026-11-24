#!/usr/bin/env python3
"""game_classes/classify.py: far-field shape class of a two-pile outcome table.

classify(T, g=None) -> dict(cls, conf, detail, scores)
  T : int8 [a][b] table, 1 = P.   g : optional Grundy table (only used as an extra feature).
  cls in {stripes, lines, cone, fractal, curved, sparse, other, chaos}.  conf in [0, 1] is a heuristic score
  (documented per class below), not a probability.  All five tests always run; if several pass the order
  lines, cone, stripes, curved, fractal breaks the tie and the others are listed in detail["also_passes"]; fallback when none passes:
  sparse (far-field P density < SPARSE_DENSITY = 0.02: "no structure found in a sparse table", NOT a positive
  finding) or, if dense, other (fewer than REGULAR_BLOCKS = 0.005 of the 4x4 far-field blocks are distinct: very
  repetitive but no class matched, a regular table the classifier cannot name) or chaos (dense and irregular).

The classes are about the far field, so everything ignores a margin near the axes:
  M = max(10, N//10): only cells with a >= M and b >= M are used (cone/fractal/box-counting see
  the whole square only where stated).

THRESHOLDS (all module constants below; every one is a judgement call, none is derived)
  SPARSE_PER_ROW = 6      lines: mean P cells per far-field row at most this.
  ANGLE_GAP = 0.03 rad    lines: P cells split into clusters where the angle atan2(b,a) jumps more
                          than this; a cluster needs >= 5 cells; clusters must cover >= 90% of P.  If a
                          cluster is not straight the gap is cut by 10 and again by 100 (families of
                          many steep lines, e.g. slopes 1+jK); curved only if no gap gives straight lines.
  LINE_RESID = 3 + 0.005 N  lines: a cluster is straight if the max |b - (s a + c)| of its fit is
                          at most this (Beatty sequences stay within 2).  Otherwise an exponent is
                          fitted (b = c0 + c1 a + c2 a^alpha, alpha in 0.2..1.6) and the cluster is
                          curved only if that fit brings the max residual under the same bound;
                          else it is not a line family at all (falls through to later tests).
  STRIPE_MISMATCH = 0.005 stripes: a shift (p,0), (0,p), (p,p), p <= PMAX_STRIPE = 256 "leaves the table
                          invariant" if at most this fraction of far-field cells change AND the
                          change is at most 10% of the random-shift baseline 2 rho (1 - rho) AND
                          at most 0.3 x the mismatch of every smaller shift (a clear dip: a smooth
                          cone changes by ~c p cells, no dip), and p = 1 only for a (nearly) constant table.
                          Stripes = two independent such shifts (a lattice, not just one line).
                          Period vector reported = smallest axis shift (p, 0), else the shifts found.
  WALL_*                  curved: rows are eventually periodic in b with one common period p*
                          (smallest p <= 60 with the last N/4 columns p-periodic, most common value
                          over rows M..N/2).  W(a) = first column from which the row is p*-periodic,
                          measured from the diagonal.  "Risers" = records of the cumulative max of
                          W over rows (first row reaching a new level; consecutive records < 4 rows
                          apart are merged, the first record is dropped as it is the window start).
                          Need >= 4 risers and growth of W of >= 3 p*.  Fit a = a0 + c W^beta
                          (beta in 0.5..4, step .05), alpha = 1/beta.  Range = betas with
                          SSE <= 1.25 SSEmin + 4 n  (4 = (2 rows)^2 of riser noise), computed for the
                          full riser set and for 5 sub-windows (first/last/middle 2/3, drop first, drop
                          last); the reported alpha_range is the UNION over windows (alpha_windows has each).
                          Curved if alpha = 1 is outside the union and alpha_best <= 0.85; beta ~ 1 is a
                          straight wall (-> cone test).
  CONE_*                  cone: far-field P density in 180 angular bins (cells with |a - b| <= 1 left
                          out).  Transitions = jumps of > 0.4 in density between adjacent plateaus
                          (greedy plateaus: bin joins plateau while within 0.15 of plateau mean; consecutive plateaus of > 3
                          bins (small ones between are ignored) whose means differ by <= 0.4 are then merged).
                          Cone needs 2..8 plateaus, every transition within <= 6 bins (3 degrees), and plateau
                          residual rms <= 0.1.  Slopes = tan(theta) of the interpolated mid-crossings.
  FRACTAL_*               fractal: box-counting of P on the largest aligned 2^m square, boxes of side
                          2..2^(m-3); local slopes of log count vs log(1/side) in [1.2, 1.85], spread
                          <= 0.3 over >= 4 scales, and far-field P density <= 0.3 (a solid wedge plus
                          boundary gives box slopes near 1.8 too, so dense tables are excluded).
  chaos conf              0.3 + 0.3 * (distinct 4x4 far-field blocks / blocks, capped at 1): never
                          above 0.6 because "chaos" only means "no structured class matched".
Confidences: stripes = 1 - mismatch/baseline (best shift pair); lines = P-cell coverage (halved if
curved); curved = 1 - SSEmin/SSE(beta=1) times fraction of rows with the common tail; cone = 1 -
(plateau rms / 0.1) times 1 - mean transition width/8; fractal = linearity of box counts.
"""
import numpy as np

SPARSE_PER_ROW = 6
ANGLE_GAP = 0.03
STRIPE_MISMATCH = 0.005
PMAX_STRIPE = 256
PMAX_TAIL = 120
REGULAR_BLOCKS = 0.005  # dense, nothing matched, and fewer than this fraction of 4x4 blocks distinct: 'other'
SPARSE_DENSITY = 0.02  # far-field P density below this and nothing structured matched: 'sparse'
BINS = 180


def _margin(N):
    return max(10, N // 10)


# ------------------------------------------------------------------ lines
def _fit_alpha(x, y, grid=np.arange(0.2, 1.61, 0.05)):
    """y = c0 + c1 x + c2 x^alpha: returns best alpha and the range within 1.25 SSEmin + n."""
    out = []
    x = x / max(x.max(), 1)  # keep the design matrix well scaled
    for al in grid:
        X = np.c_[np.ones_like(x), x, x ** al]
        co = np.linalg.lstsq(X, y, rcond=None)[0]
        e = X @ co - y
        if np.isfinite(e).all():
            out.append((al, float((e ** 2).sum()), float(np.abs(e).max())))
    if not out:
        return 1.0, (1.0, 1.0), float("inf")
    best = min(out, key=lambda t: t[1])
    ok = [al for al, s, _ in out if s <= 1.25 * best[1] + len(x)]
    return float(best[0]), (float(min(ok)), float(max(ok))), best[2]


def test_lines(P, N, M):
    n = int(P[M:, M:].sum())
    if n == 0 or n / (N - M + 1) > SPARSE_PER_ROW:  # checked first: nonzero() on a dense table is huge
        return False, 0, {}
    a, b = np.nonzero(P[M:, M:] == 1)
    a = a + M
    b = b + M
    th = np.arctan2(b, a)
    order = np.argsort(th)
    th, a, b = th[order], a[order], b[order]
    best = None
    for gap in (ANGLE_GAP, ANGLE_GAP / 10, ANGLE_GAP / 100):
        cuts = np.nonzero(np.diff(th) > gap)[0] + 1
        clusters = [(x, y) for x, y in zip(np.split(a, cuts), np.split(b, cuts)) if len(x) >= 5]
        cover = sum(len(x) for x, _ in clusters) / n
        if cover < 0.9 or not clusters:
            continue
        lines, straight = [], True
        for x, y in clusters:
            s, c = np.polyfit(x, y, 1)
            res = float(np.abs(y - (s * x + c)).max())
            item = dict(slope=float(s), intercept=float(c), resid=res, n=len(x))
            if res > 3 + 0.005 * N:
                straight = False
                item["alpha"], item["alpha_range"], cres = _fit_alpha(x.astype(float), y.astype(float))
                item["curve_resid"] = cres
                if cres > 3 + 0.005 * N:  # not even a power-law curve explains this cluster
                    lines = None
                    break
            lines.append(item)
        if lines is None:
            continue
        lines.sort(key=lambda d: d["slope"])
        det = dict(lines=lines, slopes=[round(d["slope"], 4) for d in lines], gap=gap)
        if straight:
            return True, cover, det
        if best is None:
            best = (cover / 2, dict(det, curved_lines=True))
    if best is None:
        return False, 0, {}
    return True, best[0], best[1]


# ---------------------------------------------------------------- stripes
def _shift_mismatch(P, M, E, dp, dq, p):
    """Fraction of far-field cells that change under the shift (dp p, dq p): estimated on every 8th row
    first, exactly only if that estimate is already small."""
    X = P[M:E:8, M:E]
    Y = P[M + dp * p:E + dp * p:8, M + dq * p:E + dq * p]
    est = float((X != Y).mean())
    if est > 3 * STRIPE_MISMATCH:
        return est
    return float((P[M:E, M:E] != P[M + dp * p:E + dp * p, M + dq * p:E + dq * p]).mean())


def test_stripes(P, N, M):
    """Doubly periodic far field.  A shift p is accepted only if it is a clear dip: its mismatch is
    <= STRIPE_MISMATCH, <= 10% of the random-shift baseline, and <= 0.3 x every smaller shift's mismatch
    (a smooth cone changes by about c p cells, so no shift is a dip; this is what keeps the class
    independent of the order in which the tests run).  A shift of 1 is only a dip for an (almost)
    constant table."""
    pmax = min(PMAX_STRIPE, (N - M) // 3)
    E = N + 1 - pmax
    rho = float(P[M:E, M:E].mean())
    base = 2 * rho * (1 - rho)
    if base == 0 and rho == 0:  # no P at all: trivially periodic
        return True, 1.0, dict(density=rho, shifts={}, period=(1, 1))
    found = {}
    for fam, (dp, dq) in (("a", (1, 0)), ("b", (0, 1)), ("d", (1, 1))):
        smallest = float("inf")
        for p in range(1, pmax + 1):
            mis = _shift_mismatch(P, M, E, dp, dq, p)
            if mis <= STRIPE_MISMATCH and mis <= 0.1 * base and mis <= 0.3 * smallest:
                if p > 1 or rho <= 0.01 or rho >= 0.99:
                    found[fam] = (p, mis, 1 - (mis / base if base else 0))
                break
            smallest = min(smallest, mis)
    rank2 = ("a" in found and "b" in found) or ("a" in found and "d" in found) or \
            ("b" in found and "d" in found)
    det = dict(density=rho, shifts={k: v[0] for k, v in found.items()})
    if not rank2:
        return False, 0, det
    det["period"] = (found["a"][0], found["b"][0] if "b" in found else found["a"][0]) \
        if "a" in found else tuple(sorted(v[0] for v in found.values()))[:2]
    return True, min(v[2] for v in found.values()), det


# ------------------------------------------------------------------ wall
def test_wall(P, N, M):
    """Eventually-periodic rows with a growing settling boundary W(a)."""
    L = N // 4
    pmax = min(PMAX_TAIL, L // 4)
    rows = range(M, N - L)
    if len(rows) < 20:
        return None
    ps = {}
    for a in rows:
        r = P[a]
        for p in range(1, pmax + 1):
            if (r[N - L:N + 1 - p] == r[N - L + p:N + 1]).all():
                ps[a] = p
                break
    if not ps:
        return None
    vals, cnt = np.unique(list(ps.values()), return_counts=True)
    p = int(vals[cnt.argmax()])
    Wl, al = [], []
    for a in range(M, N + 1):
        r = P[a]
        eq = r[:N + 1 - p] == r[p:]
        bad = np.nonzero(~eq)[0]
        bs = int(bad[-1]) + 1 if len(bad) else 0
        if bs <= N - L and bs >= a:
            Wl.append(bs - a)
            al.append(a)
    if len(al) < 0.5 * (N - M):
        return None
    al, Wl = np.array(al), np.array(Wl)
    cm = np.maximum.accumulate(Wl)
    rec = [0] + [i for i in range(1, len(cm)) if cm[i] > cm[i - 1]]
    pts = []
    for j, i in enumerate(rec):
        if j + 1 < len(rec) and al[rec[j + 1]] - al[i] < 4:
            continue
        pts.append((al[i], cm[i]))
    pts = pts[1:]
    det = dict(p=p, rows=len(al), risers=len(pts), Wmax=int(cm[-1]), Wmin=int(Wl[:max(1, len(Wl) // 8)].min()))
    if len(pts) < 4 or cm[-1] - Wl[:max(1, len(Wl) // 8)].min() < 3 * p:
        det["verdict"] = "none"
        return det
    A = np.array([x for x, _ in pts], float)
    W = np.array([w for _, w in pts], float)

    def fit(A, W):
        sse = {}
        for be in np.arange(0.5, 4.001, 0.05):
            X = np.c_[np.ones_like(W), W ** be]
            co = np.linalg.lstsq(X, A, rcond=None)[0]
            sse[round(float(be), 2)] = float(((X @ co - A) ** 2).sum())
        bbest = min(sse, key=sse.get)
        rng = [be for be, s in sse.items() if s <= 1.25 * sse[bbest] + 4 * len(A)]
        return bbest, rng, sse
    bbest, rng, sse = fit(A, W)
    smin = sse[bbest]
    # windows over the risers: all, first 2/3, last 2/3, middle 2/3, drop first, drop last.  The reported
    # range is the union of the per-window ranges, so it contains the spread between windows.
    n = len(A)
    k = max(4, int(np.ceil(2 * n / 3)))
    wins = {"all": (0, n), "first": (0, k), "last": (n - k, n), "mid": ((n - k) // 2, (n - k) // 2 + k),
            "drop_first": (1, n), "drop_last": (0, n - 1)}
    win_alpha = {}
    lo, hi = 1 / max(rng), 1 / min(rng)
    for nm, (i0, i1) in wins.items():
        if i1 - i0 < 4 or nm == "all":
            continue
        bb, rg_, _ = fit(A[i0:i1], W[i0:i1])
        win_alpha[nm] = (round(1 / bb, 3), round(1 / max(rg_), 3), round(1 / min(rg_), 3))
        lo, hi = min(lo, 1 / max(rg_)), max(hi, 1 / min(rg_))
    det.update(alpha=1 / bbest, alpha_range=(lo, hi), alpha_range_all=(1 / max(rng), 1 / min(rng)),
               alpha_windows=win_alpha, sse_min=smin,
               sse_linear=sse[1.0], points=[(int(x), int(w)) for x, w in zip(A, W)])
    if hi < 1.0 - 1e-9 and 1 / bbest <= 0.85:
        det["verdict"] = "curved"
        det["conf"] = float(np.clip(1 - smin / max(sse[1.0], 1e-9), 0, 1) * len(al) / (N + 1 - M))
    else:
        det["verdict"] = "straight"
    return det


# ------------------------------------------------------------------- cone
def test_cone(P, N, M):
    # angular bins over the far field, accumulated in row chunks (memory O(chunk * N), not O(N^2))
    t0, t1 = float(np.arctan2(M, N)), float(np.arctan2(N, M))
    cnt = np.zeros(BINS, dtype=np.int64)
    wsum = np.zeros(BINS)
    cols = np.arange(M, N + 1)
    for r0 in range(M, N + 1, 256):
        rows = np.arange(r0, min(r0 + 256, N + 1))
        sel = np.abs(rows[:, None] - cols[None, :]) > 1
        th = np.arctan2(cols[None, :] + 0 * rows[:, None], rows[:, None] + 0 * cols[None, :])[sel]
        v = (P[rows[0]:rows[-1] + 1, M:][sel] == 1).astype(float)
        idx = np.minimum(((th - t0) / (t1 - t0) * BINS).astype(int), BINS - 1)
        cnt += np.bincount(idx, minlength=BINS)
        wsum += np.bincount(idx, weights=v, minlength=BINS)
    den = wsum / np.maximum(cnt, 1)
    ok = cnt > 20
    den = den[ok]
    centres = (t0 + (np.nonzero(ok)[0] + 0.5) * (t1 - t0) / BINS)
    plat = [[0]]
    for i in range(1, len(den)):
        m = den[plat[-1]].mean()
        if abs(den[i] - m) <= 0.15:
            plat[-1].append(i)
        else:
            plat.append([i])
    big, small = [], []
    for pl in plat:
        if len(pl) <= 3:
            small.append(pl)
        elif big and abs(den[big[-1]].mean() - den[pl].mean()) <= 0.4:
            big[-1] = big[-1] + pl  # neighbouring (small plateaus between them are ignored) plateaus of similar density are one sector
        else:
            big.append(pl)
    det = dict(plateaus=len(big), densities=[round(float(den[pl].mean()), 3) for pl in big])
    if len(big) < 2 or len(big) > 8:
        return False, 0, det
    rms = float(np.sqrt(np.mean(np.concatenate([(den[pl] - den[pl].mean()) ** 2 for pl in big]))))
    slopes, widths = [], []
    for p1, p2 in zip(big[:-1], big[1:]):
        m1, m2 = den[p1].mean(), den[p2].mean()
        if abs(m1 - m2) <= 0.4:
            return False, 0, det
        gap = p2[0] - p1[-1] - 1
        widths.append(gap)
        # interpolate where density crosses the midpoint between the last/first bins
        i1, i2 = p1[-1], p2[0]
        mid = (m1 + m2) / 2
        seg = np.arange(i1, i2 + 1)
        d = den[seg]
        x = centres[seg]
        cross = None
        for k in range(len(seg) - 1):
            if (d[k] - mid) * (d[k + 1] - mid) <= 0 and d[k] != d[k + 1]:
                cross = x[k] + (mid - d[k]) / (d[k + 1] - d[k]) * (x[k + 1] - x[k])
                break
        if cross is None:
            cross = (x[0] + x[-1]) / 2
        slopes.append(float(np.tan(cross)))
    det.update(slopes=[round(s, 4) for s in slopes], rms=rms, widths=widths)
    if rms > 0.1 or max(widths) > 6:
        return False, 0, det
    conf = float(np.clip((1 - rms / 0.1) * (1 - np.mean(widths) / 8), 0, 1))
    return True, conf, det


# ---------------------------------------------------------------- fractal
def test_fractal(P, N, M):
    m = int(np.floor(np.log2(N + 1)))
    S = 2 ** m
    Q = (P[:S, :S] == 1)
    if not Q.any():
        return False, 0, {}
    xs, cs = [], []
    for j in range(1, m - 2):
        s = 2 ** j
        B = Q.reshape(S // s, s, S // s, s).any(axis=(1, 3))
        xs.append(np.log(1.0 / s))
        cs.append(np.log(B.sum()))
    xs, cs = np.array(xs), np.array(cs)
    if len(xs) < 4:
        return False, 0, {}
    loc = np.diff(cs) / np.diff(xs)
    D = float(np.polyfit(xs, cs, 1)[0])
    res = cs - np.polyval(np.polyfit(xs, cs, 1), xs)
    det = dict(D=D, local=[round(float(x), 3) for x in loc])
    dens = float(Q[M:, M:].mean())
    det["density"] = dens
    if 1.2 <= loc.min() and loc.max() <= 1.85 and loc.max() - loc.min() <= 0.3 and dens <= 0.3:
        return True, float(max(0, 1 - np.abs(res).max() / 0.3)), det
    return False, 0, det


# ------------------------------------------------------------ grundy extra
def grundy_scaling(g, N, M):
    """Fraction of far-field cells with g(2a, 2b) == 2 g(a, b): 1.0 for Nim (XOR)."""
    h = N // 2
    a = np.arange(M, h + 1)
    X = g[np.ix_(a, a)]
    Y = g[np.ix_(2 * a, 2 * a)]
    return float((Y == 2 * X).mean())


# ----------------------------------------------------------------- driver
PRECEDENCE = ("lines", "cone", "stripes", "curved", "fractal")


def classify(T, g=None):
    """Runs every test (none is skipped), so the class cannot depend on test order.  If more than one
    test passes, the first in PRECEDENCE wins and detail["also_passes"] lists the others (an ambiguity
    the census counts; the test suite requires none on the named games)."""
    T = np.asarray(T)
    N = T.shape[0] - 1
    M = _margin(N)
    P = (T == 1).astype(np.int8)
    P[T == -1] = 0
    scores, detail, passed = {}, {}, {}

    ok, conf, det = test_lines(P, N, M)
    scores["lines"], detail["lines"] = conf, det
    if ok:
        passed["curved" if det.get("curved_lines") else "lines"] = conf
    ok, conf, det = test_cone(P, N, M)
    scores["cone"], detail["cone"] = conf, det
    if ok:
        passed["cone"] = conf
    ok, conf, det = test_stripes(P, N, M)
    scores["stripes"], detail["stripes"] = conf, det
    if ok:
        passed["stripes"] = conf
    wall = test_wall(P, N, M)
    detail["wall"] = wall
    if wall and wall.get("verdict") == "curved":
        scores["curved"] = wall["conf"]
        passed.setdefault("curved", wall["conf"])
    ok, conf, det = test_fractal(P, N, M)
    scores["fractal"], detail["fractal"] = conf, det
    if ok:
        passed["fractal"] = conf
    dens = float(P[M:, M:].mean())
    detail["density"] = dens
    if passed:
        order = [c for c in PRECEDENCE if c in passed]
        if len(order) > 1:
            detail["also_passes"] = order[1:]
        return _ret(order[0], passed[order[0]], scores, detail, g, N, M)

    X = P[M:, M:]
    h = (X.shape[0] // 4) * 4
    blk = X[:h, :h].reshape(h // 4, 4, h // 4, 4).transpose(0, 2, 1, 3).reshape(-1, 16)
    w = blk @ (1 << np.arange(16, dtype=np.int32))
    frac = len(np.unique(w)) / len(w)
    if dens < SPARSE_DENSITY:
        return _ret("sparse", 0.3, scores, detail, g, N, M, frac)
    if frac < REGULAR_BLOCKS:  # dense, locally very repetitive, but no class matched (e.g. wsub{1,4,5})
        return _ret("other", 0.3, scores, detail, g, N, M, frac)
    return _ret("chaos", 0.3 + 0.3 * min(1.0, frac), scores, detail, g, N, M, frac)


def _ret(cls, conf, scores, detail, g, N, M, blockfrac=None):
    if g is not None:
        detail["grundy_scaling"] = grundy_scaling(np.asarray(g), N, M)
    if blockfrac is not None:
        detail["block_fraction"] = blockfrac
    return dict(cls=cls, conf=round(float(conf), 3), detail=detail, scores=scores)


def summary(r):
    d = r["detail"]
    c = r["cls"]
    if c == "stripes":
        return f"period {d['stripes'].get('period')}"
    if c == "lines":
        sl = d["lines"]["slopes"]
        return "slopes " + ",".join(map(str, sl[:6])) + (f" (+{len(sl) - 6} more)" if len(sl) > 6 else "")
    if c == "cone":
        return "slopes " + ",".join(map(str, d["cone"]["slopes"]))
    if c == "curved":
        w = d.get("wall")
        if w and w.get("verdict") == "curved":
            return "alpha %.2f [%.2f,%.2f]" % ((w["alpha"],) + tuple(w["alpha_range"]))
        return "curved lines"
    if c == "fractal":
        return "D %.2f" % d["fractal"]["D"]
    return ""
