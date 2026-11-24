#!/usr/bin/env python3
"""pump2: extends the pumping certificate (pump.py) to the 12 'oblique'/'open' cases.

Finding (22 Nov 2026): most of these cases ARE block-insertion families, but only for a
larger u than segcert/slope6 searched, or only from a later onset a0.  Reasons:
  * glide: a sector anchored at a fixed wall (the diagonal d = 0, or a constant-width head) has content
    that shifts by s per u rows with s != (shift of its left wall) mod its period p.  After k = p/gcd(..)
    steps the phase returns, so u' = k*u is an insertion step (e.g. {5,6}: u 35 -> 385, v 7 -> 77).
  * phase: the inserted block must be a whole number of periods of its run (p | v), forcing u' = lcm.
  * late onset: the family only settles after a ~ 1000-5000 (e.g. {2,3,4,5,6}: fails at a0 = 600,
    holds at a0 = 1000).
So pump.prove_case is used unchanged; pump2 adds (1) a search for (u, v) on long exact rows,
(2) a choice of a0 at or after the onset, and (3) an INDEPENDENT C brute force (bf2.c) so the
symbolic family is cross-checked on rows a0 .. a0 + several u, not only on a <= 1000.

Usage: pump2.py --selftest | --one S1 S2 U V[,V2] A0 [NBF]   |  --cases  (runs the table in CASES)
"""
import sys, os, json, time, subprocess
import numpy as np
from pump import prove_case, family_row, public
from lead_a3 import Pair, Row
from segcert import align

import pump
_infer1 = pump.infer          # original, kept before use_infer2() patches pump.infer

# ---------------------------------------------------------------- inference with expected walls
def align_expect(A, B, vs, RUN, n=None):
    """Insertions [(x, v, word)] turning row A into row B, with the EXPECTED wall sizes vs in order.
    At the first mismatch d (A's run ends where B's run continues) the next expected block, or a
    merged block v_j + ... + v_k (walls j..k-1 invisible in this row), is inserted; the inserted
    cells are B's cells there and must resynchronise B with A for 4*RUN cells.  Unlike
    segcert.align, the inserted block need not be a copy of the v cells before it, so a run
    shorter than v before the wall (early rows) is allowed.  None if no fit."""
    if n is None:
        n = len(A.pre) + 4 * len(A.cyc) + 2 * sum(vs) + 50
    ins, off, d, j = [], 0, 0, 0
    while d < n:
        if B(d + off) == A(d):
            d += 1; continue
        done = False
        for k in range(j, len(vs)):
            V = sum(vs[j:k + 1])
            if all(B(d + off + V + i) == A(d + i) for i in range(min(4 * RUN, n - d))):
                w = [B(d + off + i) for i in range(V)]
                q = 0
                for jj in range(j, k + 1):
                    ins.append((d, vs[jj], tuple(w[q:q + vs[jj]]))); q += vs[jj]
                off += V; j = k + 1; done = True; break
        if not done:
            return None
    if A.cyc != B.cyc or j != len(vs):
        return None
    return ins


def infer2(A, B, vs):
    """Family R(n) = A with n copies of the inserted word I_j at each insertion point x_j:
    X_j = A[x_{j-1}, x_j), Y_j = I_j, C_j = 0.  So R(0) = A and R(1) = B by construction; the family
    is then tested on row a+2u (prove_case) and proved by the step.  Falls back to pump.infer for the
    invisible-wall case."""
    if A.key == B.key and len(vs) == 1 and vs[0] % len(A.cyc) == 0:
        return _infer1(A, B, vs)
    ins = align_expect(A, B, vs, 4 * 6 + 8)
    if ins is None:
        return None, "align_expect failed"
    X, Y, C = [], [], []
    prev = 0
    for x, v, w in ins:
        X.append(tuple(A(t) for t in range(prev, x))); Y.append(w); C.append(0); prev = x
    R = pump.Sym(X, Y, C, pump.row_drop(A, prev))
    if R.concrete(0).key != A.key or R.concrete(1).key != B.key:
        return None, "inferred family does not reproduce rows a, a+u"
    return R, None


def _run_spans(S, n):
    """[(start, end, v)] of run j in S.concrete(n)."""
    out, pos = [], 0
    for j in range(S.m):
        pos += len(S.X[j]); v = len(S.Y[j]); e = pos + (n + S.C[j]) * v
        out.append((pos, e, v)); pos = e
    return out


def fam_equal(P, Q, nmax=400):
    """Sound test that families P(n), Q(n) agree for EVERY n >= n_lo (n_lo = least n with all exponents
    >= 0).  Lemma: if P(n) == Q(n) and, for every wall j, run j of P and run j of Q overlap in >= v_j
    cells, then P(n+1) == Q(n+1) and the overlap persists.  (P(n+1) is P(n) with v_j cells inserted at
    any point p of run j with [p - v_j, p) inside it, the inserted cells being w[p - v_j, p); pick p in
    the common overlap, insert walls right to left; Q(n+1) is the same word.)  So check every n from
    n_lo up to the first n where the overlap holds.  Visible walls only (deg families: False)."""
    if P.deg or Q.deg or [len(y) for y in P.Y] != [len(y) for y in Q.Y]:
        return False
    n = max([0] + [-c for c in P.C + Q.C])
    for n in range(n, n + nmax):
        if P.concrete(n).key != Q.concrete(n).key:
            return False
        if all(min(e1, e2) - max(s1, s2) >= v for (s1, e1, v), (s2, e2, _) in zip(_run_spans(P, n), _run_spans(Q, n))):
            return True
    return False


_key1 = pump.Sym.key


class _FamKey:
    """Sym.key() replacement: equal if pump's normal forms agree, else if fam_equal proves it."""
    __slots__ = ("S", "k")

    def __init__(self, S):
        self.S, self.k = S, _key1(S)

    def __eq__(self, o):
        return self.k == o.k or fam_equal(self.S, o.S)

    def __ne__(self, o):
        return not self.__eq__(o)


def use_infer2():
    """Route pump.prove_case through infer2 and the family-equality test fam_equal (pump.py itself is
    not edited; Sym.key() is only used by prove_case's two step comparisons)."""
    pump.infer = infer2
    pump.Sym.key = lambda self: _FamKey(self)


HERE = os.path.dirname(os.path.abspath(__file__))
TMP = os.environ.get("PUMP2_TMP", os.environ.get("TMPDIR", "/tmp"))


def bf_matrix(S1, S2, N):
    """(N+1)x(N+1) uint8 outcome matrix from the C brute force (1 = P)."""
    exe = os.path.join(TMP, "bf2")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(os.path.join(HERE, "bf2.c")):
        subprocess.check_call(["cc", "-O2", "-o", exe, os.path.join(HERE, "bf2.c")])
    out = os.path.join(TMP, "bf_%s_%s_%d.bin" % ("".join(map(str, S1)), "".join(map(str, S2)), N))
    if not os.path.exists(out):
        subprocess.check_call([exe, str(N), ",".join(map(str, S1)), ",".join(map(str, S2)), out])
    return np.memmap(out, dtype=np.uint8, mode="r", shape=(N + 1, N + 1))


def row_arr(R, n):
    pre, cyc = R.pre, R.cyc
    a = np.empty(n, np.uint8)
    L = min(len(pre), n)
    a[:L] = pre[:L]
    if n > L:
        a[L:] = np.resize(np.array(cyc, np.uint8), n - L)
    return a


def crosscheck_bf(cert, N):
    """Every row a in [0, N] (family rows from a0 on) against the C brute force on all cells a <= b <= N.
    Returns (mismatching cells, rows checked)."""
    B = bf_matrix(tuple(cert["S1"]), tuple(cert["S2"]), N)
    bad = 0; nrows = 0
    for a in range(0, N + 1):                 # rows below a0 too (they come from lead_a3)
        R = family_row(cert, a)
        bad += int(np.count_nonzero(row_arr(R, N - a + 1) != B[a, a:]))
        nrows += 1
    return bad, nrows


def find_u(S1, S2, A, UMAX, NR=None, nrows=8, vmax=3000):
    """Smallest u (multiple of per g) for which rows A..A+nrows-1 map to rows +u by tandem
    insertions (segcert.align).  Exact rows; this is a search, not a proof."""
    P = Pair(S1, S2)
    NR = NR or A + UMAX + nrows + 2
    while len(P.rows) < NR:
        P.next_row()
    g = P.gper
    for u in range(g, UMAX + 1, g):
        vl = set(); ok = True
        for a in range(A, A + nrows):
            ins = align(P.rows[a], P.rows[a + u], P.M, vmax, 4 * P.M + 8)
            if ins is None or any(v % g for _, v in ins):
                ok = False; break
            vl.add(tuple(v for _, v in ins))
        if ok:
            return u, sorted(vl)
    return None, None


# (S1, S2 representative, u, v list, a0) found by find_u on rows to 12000 (scratch runs, 22 Nov 2026)
CASES = [
    ((5, 6), (2, 3, 5), 385, [77], 1540),
    ((4, 5, 6), (1, 3, 4), 308, [231], 1232),
    ((1, 4, 5, 6), (1, 2, 3, 4, 5, 6), 378, [392], 1512),
    ((2, 5, 6), (1, 4, 5, 6), 396, [693], 1584),
    ((2, 3, 4, 5, 6), (2, 5, 6), 88, [44], 1000),
    ((1, 2, 4, 5, 6), (1, 2), 330, [210], 1320),
    ((1, 2, 5, 6), (1, 2, 3, 4), 2940, [70], 5000),
    ((1, 5, 6), (2, 4), 1968, [1170], 5000),
    ((1, 3, 5, 6), (3, 6), 2070, [621], 5000),
]


def run_one(S1, S2, u, vs, a0, NBF=None):
    t = time.time()
    c = prove_case(tuple(S1), tuple(S2), u, vs, a0)
    out = public(c)
    if c["ok"]:
        N = NBF or min(a0 + 3 * u, 14000)
        bad, nrows = crosscheck_bf(c, N)
        out.update(bf_N=N, bf_rows=nrows, bf_bad=bad, ok=(bad == 0))
    out["sec"] = round(time.time() - t, 1)
    return out


def _job(args):
    if os.environ.get("PUMP2_INFER2"):
        use_infer2()
    try:
        return run_one(*args)
    except Exception as ex:
        return dict(S1=list(args[0]), S2=list(args[1]), ok=False, stage="crash", why=repr(ex))


def selftest():
    """Negative and positive controls for pump2 (infer2 + fam_equal + the C brute force)."""
    use_infer2()
    S = pump.Sym
    P = S([(0,)], [(1, 0, 0)], [0], Row((), (1,)))
    Q = S([(0, 1)], [(0, 0, 1)], [-1], Row((0, 0), (1,)))      # same family, rotated, C shifted
    R = S([(0,)], [(1, 0, 0)], [0], Row((0,), (1,)))          # different tail
    assert fam_equal(P, Q) and not fam_equal(P, R)
    print("fam_equal: rotated family accepted, different family rejected")
    c = run_one((3, 5), (1, 2), 33, [18], 300, 1000)
    print(json.dumps(c)); assert c["ok"]
    c = run_one((5, 6), (2, 3, 5), 35, [7], 1540)              # the old u: glide makes it fail
    assert not c["ok"]; print("negative control {5,6} u=35 rejected:", c.get("stage"), c.get("why"))
    def flip_x(fam):
        f = next(f for f in fam if len(f.X[0]) > 8); X = list(f.X[0]); X[8] ^= 1; f.X[0] = tuple(X)
    def flip_c(fam):
        f = next(f for f in fam if not f.deg); f.C[0] += 1
    for mu in (flip_x, flip_c):
        c = prove_case((5, 6), (2, 3, 5), 385, [77], 1540, mutate=mu)
        assert not c["ok"], mu.__name__
        print("mutation %s rejected at %s: %s" % (mu.__name__, c.get("stage"), c.get("why")))
    c = prove_case((3, 5), (1, 2), 33, [18], 300)
    f = c["_fam"][0]; X = list(f.X[0]); X[8] ^= 1; f.X[0] = tuple(X)   # corrupt a PROVED cert
    bad, _ = crosscheck_bf(c, 1000)
    assert bad > 0; print("crosscheck_bf finds the corrupted family: %d bad cells" % bad)
    print("PASS")


if __name__ == "__main__":
    a = sys.argv[1:]
    if "--infer2" in a:
        a.remove("--infer2"); use_infer2()
    if a[0] == "--selftest":
        selftest()
    elif a[0] == "--one":
        S1 = tuple(int(x) for x in a[1].split(",")); S2 = tuple(int(x) for x in a[2].split(","))
        u = int(a[3]); vs = [int(x) for x in a[4].split(",")]; a0 = int(a[5])
        NBF = int(a[6]) if len(a) > 6 else None
        print(json.dumps(run_one(S1, S2, u, vs, a0, NBF)))
    elif a[0] == "--find":
        S1 = tuple(int(x) for x in a[1].split(",")); S2 = tuple(int(x) for x in a[2].split(","))
        print(find_u(S1, S2, int(a[3]), int(a[4])))
    elif a[0] == "--cases":
        from multiprocessing import Pool
        jobs = list(CASES)
        if len(a) > 1 and a[1] == "--all-s2":     # every S2 of the census, not just the representative
            C = json.load(open(os.path.join(HERE, "raw/census42.json")))
            jobs = []
            for (S1, _, u, vs, a0) in CASES:
                c = next(c for c in C if tuple(c["S1"]) == S1 and c["status"] != "insertion"
                         and any(tuple(s) == _ for s in c["S2"]))
                jobs += [(S1, tuple(s2), u, vs, a0) for s2 in c["S2"]]
        with Pool(min(6, len(jobs))) as p:
            for r in p.imap_unordered(_job, jobs):
                print(json.dumps(r), flush=True)
