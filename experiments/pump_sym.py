#!/usr/bin/env python3
"""Hardened pumping certificate: the step of pump.py proved SYMBOLICALLY in n (22 Nov 2026).

pump.py (H.E) proves block insertion for 56 pairs Sub(S1) -push-> Sub(S2), but one step of its
argument was only checked at two values of n: that the columns F reads split as
    G0 . Q1^(n+e1) . G1 . ... . Qm^(n+em) . Rest
with G_j, Q_j, Rest independent of n.  This module never evaluates a family row at a concrete n
inside the step.  Instead every input cell F reads is ADDRESSED symbolically.

Setting.  Family row R_i(n) = X0 Y0^(n+C0) X1 ... Y_{m-1}^(n+C_{m-1}) Z  (or X0..X_{m-1} Y^inf if the
last wall is invisible), |Y_j| = v_j for EVERY class.  Row a = a0+i+n*u.  Row a-k (k >= 1) is
R_{(i-k) mod u}(n - delta_k), delta_k = -floor((i-k)/u).

Layout lemma (exact, affine in n).  In R(n - delta) the segments X_j, Y_j-run, Z start and end at
positions c + k*n with explicit integers c, k (k = v_0+...+v_{j-1} for the start of run j), valid
whenever every exponent n - delta + C_j >= 0.

Address lemma (`lookup`).  F reads input cells at positions p(n) = c + k*n.  For a threshold N we
find the segment containing p(N) and CHECK, by affine arithmetic:
    p - start has slope >= 0 and is >= 0 at N;   end - p - 1 has slope >= 0 and is >= 0 at N
so p(n) lies in that segment for EVERY n >= N; and
    X or Z segment: slope(p) == slope(start)          (offset constant)
    Y_j run:        slope(p) - slope(start) = 0 mod v_j  (offset mod v_j constant)
so the letter read is the same for every n >= N.  Nothing is evaluated at a second n.

Step lemma (`sym_step`), for class i and all n >= N:
  * run j of every input (s in S1) occupies stream columns [alpha_s + n V_j, beta_s + n V_{j+1});
    slopes are checked equal across inputs.  A_j = max alpha_s (A_0 >= M), B_j = min beta_s,
    e_j = floor((B_j - A_j)/v_j).  The Q_j region [A_j + n V_j, A_j + e_j v_j + n V_{j+1}) holds
    exactly n + e_j blocks of v_j columns and lies inside every input's run j (checked), so every
    block carries the same letters (read once, by lookup of block 0).
  * g-letters: g(a + col) with u, V_j = 0 mod per(g) (checked) depend only on (a0+i+c) mod per(g).
  * G0 (columns < A_0, incl. the near-diagonal cells r_{a-k}(k)), gaps G_j and the head of Rest are
    read cell by cell through `lookup`; the tail of Rest is an n-independent eventually periodic
    word (each input read inside its Z, or inside an infinite last run).
  * F's state at block boundaries: iterate T (one block) from the n-independent entry state until
    it repeats; period 1 after tau_j blocks is required.  If n + e_j >= tau_j (an obligation) the
    Q_j output is outs[:tau] . outs[tau]^(n + e_j - tau).
  * The output is therefore the symbolic row Out = Sym(X', Y', C', Z') for every n >= N, and
    normal-form equality Out == R_i (with all exponents >= 0, obligations) gives row a = R_i(n).
Induction: rows a0 .. a0 + (N*+2)u + M equal the family (exact rows, lead_a3); for a beyond,
rows a-1..a-M are earlier family rows (N* u >= M is checked), so the step lemma applies.

Every obligation is recorded; `--selftest` also stress-tests `lookup` and `sym_step` against
concrete evaluation (as a test of the code, not as part of the proof) and checks negative controls.

Usage: pump_sym.py --selftest | --one S1 S2 U V[,V2] [A0] | --census [CENSUS_JSON] [OUT_JSONL]
"""
import sys, json, os, random, time
from math import lcm
from lead_a3 import Pair, Row
from pump import Sym, infer, row_drop, crosscheck, public


class SymFail(Exception):
    pass


class Ob:
    """Obligation ledger: every check 'c + k n >= 0 for all n >= N' or structural equality."""

    def __init__(self, N):
        self.N = N; self.n_aff = 0; self.n_eq = 0

    def ge(self, c, k, what):
        """c + k*n >= 0 for every n >= N  <=>  k >= 0 and c + k*N >= 0."""
        self.n_aff += 1
        if k < 0 or c + k * self.N < 0:
            raise SymFail("obligation fails: %s (c=%d, k=%d, N=%d)" % (what, c, k, self.N))

    def eq(self, x, y, what):
        self.n_eq += 1
        if x != y:
            raise SymFail("structural check fails: %s (%r != %r)" % (what, x, y))


# ---------------------------------------------------------------- layout and addressing
def layout(R, dl, ob):
    """Segments of R(n - dl): list of (kind, j, start, end) with start/end affine (c, k); end None
    means unbounded.  Records the exponent obligations n - dl + C_j >= 0."""
    segs = []; c = k = 0
    for j in range(R.m):
        L = len(R.X[j])
        segs.append(("X", j, (c, k), (c + L, k))); c += L
        v = len(R.Y[j])
        if R.deg and j == R.m - 1:
            segs.append(("Y", j, (c, k), None))
            return segs
        e = R.C[j] - dl
        ob.ge(e, 1, "input exponent")
        st = (c, k); c += e * v; k += v
        segs.append(("Y", j, st, (c, k)))
    segs.append(("Z", None, (c, k), None))
    return segs


def lookup(R, dl, p, ob, want_tail=False):
    """Letter of R(n - dl) at position p(n) = p[0] + p[1] n, PROVED constant for all n >= ob.N.
    want_tail: also return the n-independent eventually periodic suffix from p when p lies in Z or
    in an unbounded last run (else None)."""
    N = ob.N
    pN = p[0] + p[1] * N
    if pN < 0:
        raise SymFail("negative position")
    for kind, j, st, en in layout(R, dl, ob):
        sN = st[0] + st[1] * N
        if not (sN <= pN and (en is None or pN < en[0] + en[1] * N)):
            continue
        ob.ge(p[0] - st[0], p[1] - st[1], "p >= segment start")
        if en is not None:
            ob.ge(en[0] - p[0] - 1, en[1] - p[1], "p < segment end")
        o0, o1 = p[0] - st[0], p[1] - st[1]
        if kind == "X":
            ob.eq(o1, 0, "X offset constant")
            return R.X[j][o0], None
        if kind == "Y":
            Y = R.Y[j]; v = len(Y)
            ob.eq(o1 % v, 0, "run offset constant mod v")
            o = o0 % v
            tail = Row((), Y[o:] + Y[:o]) if (want_tail and en is None) else None
            return Y[o], tail
        ob.eq(o1, 0, "Z offset constant")
        return R.Z(o0), (row_drop(R.Z, o0) if want_tail else None)
    raise SymFail("position in no segment")


def run_bounds(R, dl, j, ob):
    for kind, jj, st, en in layout(R, dl, ob):
        if kind == "Y" and jj == j:
            return st, en
    raise SymFail("no run %d" % j)


# ---------------------------------------------------------------- the symbolic step
def sym_step(P, fam, i, a0, u, vs, N):
    """Prove: for every n >= N, F applied to the family inputs of class i outputs R_i(n).
    Returns (out Sym, info) or raises SymFail."""
    ob = Ob(N)
    S1, M, gp = P.S1, P.M, P.gper
    ob.eq(P.gpre, 0, "g purely periodic"); ob.eq(u % gp, 0, "per g | u")
    m = len(vs); V = [sum(vs[:j]) for j in range(m + 1)]
    for v in vs:
        ob.eq(v % gp, 0, "per g | v")

    def src(k):                          # row a-k = R_{(i-k) mod u}(n - delta)
        j = i - k
        return fam[j % u], -(j // u)

    def gd(c, k):                        # [g(a) != g(a + col)], col = c + k n
        ob.eq(k % gp, 0, "g-column slope = 0 mod per g")
        return P.g[(a0 + i) % gp] != P.g[(a0 + i + c) % gp]

    ins = {s: src(s) for s in S1}
    for s in S1:
        R, dl = ins[s]
        ob.eq(R.m, m, "walls of input row")
        ob.eq([len(y) for y in R.Y], list(vs), "wall sizes of input row")

    # run j of input s in stream coordinates: [alpha, beta)
    A, B = [], []
    for j in range(m):
        al, be = [], []
        for s in S1:
            R, dl = ins[s]
            st, en = run_bounds(R, dl, j, ob)
            ob.eq(st[1], V[j], "run start slope")
            al.append(st[0] - s)
            if en is not None:
                ob.eq(en[1], V[j + 1], "run end slope")
                be.append(en[0] - s)
            else:
                ob.eq(j, m - 1, "only the last run may be unbounded")
        A.append(max(al)); B.append(min(be) if be else None)
    A[0] = max(A[0], M)

    def cell(state, col, inp):
        if not gd(*col):
            return 0
        for s in S1:
            if inp[s] == 1 or state[M - s] == 1:
                return 0
        return 1

    def letters(col):                    # input letters r_{a-s}(col+s), col affine
        return {s: lookup(ins[s][0], ins[s][1], (col[0] + s, col[1]), ob)[0] for s in S1}

    # G0: columns 0 .. A_0 - 1 (slope 0), with the near-diagonal rule for d < s
    r = []
    for d in range(A[0]):
        if not gd(d, 0):
            r.append(0); continue
        c = 1
        inp = letters((d, 0))
        for s in S1:
            if inp[s] == 1:
                c = 0; break
            if d >= s:
                if r[d - s] == 1:
                    c = 0; break
            else:
                Rk, dk = src(s - d)
                if lookup(Rk, dk, (s - d, 0), ob)[0] == 1:
                    c = 0; break
        r.append(c)
    state = tuple(r[-M:])
    X = [tuple(r)]; Y = []; C = []; taus = []; deg = False; Z = None
    for j in range(m):
        v = vs[j]
        inf = B[j] is None
        e = None if inf else (B[j] - A[j]) // v
        # Q_j region lies inside every input's run j, for all n >= N
        for s in S1:
            R, dl = ins[s]
            st, en = run_bounds(R, dl, j, ob)
            ob.ge(A[j] - (st[0] - s), V[j] - st[1], "Q region starts inside run")
            if not inf:
                if en is None:
                    pass                  # unbounded run contains everything after its start
                else:
                    ob.ge((en[0] - s) - (A[j] + e * v), en[1] - V[j + 1], "Q region ends inside run")
            else:
                ob.eq(en, None, "infinite Q region needs unbounded runs")
        if not inf:
            ob.ge(e, 1, "Q region has n + e >= 0 blocks")
        # the block letters (block 0 of the region; all blocks equal by run periodicity)
        blk = [letters((A[j] + t, V[j])) for t in range(v)]
        gblk = [gd(A[j] + t, V[j]) for t in range(v)]
        seen = {}; sts = []; outs = []
        while state not in seen:
            seen[state] = len(sts); sts.append(state)
            w = []
            for t in range(v):
                if not gblk[t]:
                    b = 0
                else:
                    b = 1
                    for s in S1:
                        if blk[t][s] == 1 or state[M - s] == 1:
                            b = 0; break
                w.append(b); state = state[1:] + (b,)
            outs.append(tuple(w))
        tau = seen[state]
        if len(sts) - tau != 1:
            raise SymFail("block-boundary state cycles with period %d" % (len(sts) - tau))
        state = sts[tau]
        X[-1] = X[-1] + tuple(x for w in outs[:tau] for x in w)
        Y.append(outs[tau]); taus.append(tau)
        if inf:
            deg = True; C.append(0)
            break
        ob.ge(e - tau, 1, "n + e_j >= tau_j")
        C.append(e - tau)
        gs = A[j] + e * v                # next columns: gs + t + n V_{j+1}
        if j + 1 < m:
            L = A[j + 1] - gs
            ob.ge(L, 0, "gap length >= 0")
            w = []
            for t in range(L):
                col = (gs + t, V[j + 1])
                b = cell(state, col, letters(col)); w.append(b); state = state[1:] + (b,)
            X.append(tuple(w))
        else:
            # Rest: each input as an n-independent eventually periodic word
            tails = {}
            for s in S1:
                R, dl = ins[s]
                pre = []; t = 0
                while True:
                    let, tl = lookup(R, dl, (gs + t + s, V[m]), ob, want_tail=True)
                    if tl is not None:
                        tails[s] = Row(tuple(pre) + tl.pre, tl.cyc); break
                    pre.append(let); t += 1
                    if t > 10 ** 6:
                        raise SymFail("Rest: no tail")
            ob.eq(V[m] % gp, 0, "Rest slope")
            D0 = max(len(x.pre) for x in tails.values()) + M
            Lc = lcm(*[len(x.cyc) for x in tails.values()], gp)
            seen2 = {}; w = []; t = 0
            while True:
                if t >= D0:
                    key = (state, t % Lc)
                    if key in seen2:
                        jj = seen2[key]; Z = Row(tuple(w[:jj]), tuple(w[jj:t])); break
                    seen2[key] = t
                col = (gs + t, V[m])
                b = cell(state, col, {s: tails[s](t) for s in S1})
                w.append(b); state = state[1:] + (b,); t += 1
    if deg:
        out = Sym(X, Y, C, Row((), Y[-1]), deg=True)
    else:
        out = Sym(X, Y, C, Z)
    # exponent obligations of the claimed equality
    for jj in range(out.m - (1 if out.deg else 0)):
        ob.ge(out.C[jj], 1, "output exponent")
    R = fam[i]
    for jj in range(R.m - (1 if R.deg else 0)):
        ob.ge(R.C[jj], 1, "family exponent")
    if out.key() != R.key():
        raise SymFail("F(family) != family for class %d" % i)
    return out, dict(tau=taus, n_aff=ob.n_aff, n_eq=ob.n_eq, A=A, B=B)


# ---------------------------------------------------------------- the whole proof for one pair
def build_family(P, u, vs, a0):
    M = P.M
    while len(P.rows) < a0 + 3 * u + M:
        P.next_row()
    fam = []
    for i in range(u):
        R, err = infer(P.rows[a0 + i], P.rows[a0 + i + u], vs)
        if R is None:
            return None, dict(stage="infer", cls=i, why=err)
        if R.concrete(2).key != P.rows[a0 + i + 2 * u].key:
            return None, dict(stage="infer", cls=i, why="row a0+i+2u breaks the family")
        fam.append(R)
    return fam, None


def prove_sym(S1, S2, u, vs, a0=None, mutate=None, NMAX=40, base_extra=2):
    P = Pair(S1, S2)
    res = dict(S1=list(S1), S2=list(S2), u=u, v=list(vs))
    if a0 is None:
        a0 = max(4 * u, 300)
    res["a0"] = a0
    if P.gpre != 0 or u % P.gper or any(v % P.gper for v in vs):
        return dict(res, ok=False, stage="setup", why="g / per(g) conditions")
    fam, err = build_family(P, u, vs, a0)
    if fam is None:
        return dict(res, ok=False, **err)
    if mutate:
        mutate(fam)
    Ns, taus, n_aff, n_eq = [], [], 0, 0
    for i in range(u):
        last = None; out = None
        for N in range(1, NMAX + 1):
            try:
                out, info = sym_step(P, fam, i, a0, u, vs, N)
                break
            except SymFail as ex:
                last = str(ex)
                if last.startswith("F(family)") or last.startswith("block-boundary"):
                    break                 # these do not depend on N: a real failure
        if out is None:
            return dict(res, ok=False, stage="step", cls=i, why=last)
        Ns.append(N); taus.append(info["tau"]); n_aff += info["n_aff"]; n_eq += info["n_eq"]
    Nstar = max(Ns)
    if Nstar * u < P.M:
        return dict(res, ok=False, stage="induction", why="N* u < M")
    NB = a0 + (Nstar + base_extra) * u + P.M
    while len(P.rows) < NB:
        P.next_row()
    for a in range(a0, NB):
        i, n = (a - a0) % u, (a - a0) // u
        if fam[i].concrete(n).key != P.rows[a].key:
            return dict(res, ok=False, stage="base", row=a, why="concrete row differs from family")
    return dict(res, ok=True, Nstar=Nstar, base_rows=[a0, NB], max_tau=max(max(t) for t in taus),
                obligations_affine=n_aff, obligations_struct=n_eq, _P=P, _fam=fam)


# ---------------------------------------------------------------- tests of the code
def concrete_F(P, a, rows_of):
    """Row a by the transducer rule from concrete rows rows_of(a-k) (a >= M).  Test oracle only."""
    S1, M = P.S1, P.M
    ins = {s: rows_of(a - s) for s in S1}
    near = {k: rows_of(a - k) for k in range(1, M + 1)}
    D0 = max(len(x.pre) for x in ins.values()) + 2 * M
    L = lcm(*[len(x.cyc) for x in ins.values()], P.gper)
    r = []; seen = {}; d = 0
    while True:
        if d >= D0:
            key = (tuple(r[d - M:d]), d % L)
            if key in seen:
                j = seen[key]; return Row(r[:j], r[j:d])
            seen[key] = d
        c = 1
        if P.gval(a) == P.gval(a + d):
            c = 0
        else:
            for s in S1:
                if ins[s](d + s) == 1 or (r[d - s] == 1 if d >= s else near[s - d](s - d) == 1):
                    c = 0; break
        r.append(c); d += 1


def test_lookup(trials=3000, seed=1):
    """Whenever lookup succeeds at N, the letter must equal concrete evaluation at N..N+12."""
    rnd = random.Random(seed); ok = fail = 0
    for _ in range(trials):
        m = rnd.choice([1, 1, 2]); vs = [rnd.randint(1, 5) for _ in range(m)]
        X = [tuple(rnd.randint(0, 1) for _ in range(rnd.randint(0, 6))) for _ in range(m)]
        Y = [tuple(rnd.randint(0, 1) for _ in range(v)) for v in vs]
        C = [rnd.randint(-2, 3) for _ in range(m)]
        deg = rnd.random() < 0.2
        Z = Row(tuple(rnd.randint(0, 1) for _ in range(rnd.randint(0, 5))),
                tuple(rnd.randint(0, 1) for _ in range(rnd.randint(1, 4))))
        if deg:
            Z = Row((), Y[-1])
        R = Sym(X, Y, C, Z, deg=deg)
        dl = rnd.randint(0, 1)
        V = sum(vs)
        p = (rnd.randint(-3, 40), rnd.choice([0, 1, vs[0], V, V + vs[-1], 2 * V]))
        N = rnd.randint(3, 8)
        try:
            let, _ = lookup(R, dl, p, Ob(N))
        except SymFail:
            fail += 1; continue
        for n in range(N, N + 13):
            assert R.concrete(n - dl)(p[0] + p[1] * n) == let, (R.X, R.Y, R.C, deg, dl, p, N, n)
        ok += 1
    return ok, fail


def test_step_concrete(cert, ns=(0, 1, 3, 7)):
    """Concrete F on concrete family rows at n = N*+k equals the family row (test only)."""
    P, fam, a0, u = cert["_P"], cert["_fam"], cert["a0"], cert["u"]
    def rows_of(b):
        return fam[(b - a0) % u].concrete((b - a0) // u)
    bad = 0
    for i in range(u):
        for k in ns:
            n = cert["Nstar"] + k
            a = a0 + i + n * u
            if concrete_F(P, a, rows_of).key != rows_of(a).key:
                bad += 1
    return bad


def selftest():
    t = time.time()
    ok, fail = test_lookup()
    print("lookup stress: %d proved lookups all agree with concrete n = N..N+12 (%d refused)" % (ok, fail))
    assert ok > 1000
    c = prove_sym((3, 5), (1, 2), 33, [18])
    print(json.dumps(public(c)))
    assert c["ok"], c
    # same family as pump.py and same base
    from pump import prove_case
    c0 = prove_case((3, 5), (1, 2), 33, [18])
    assert c0["ok"] and all(a.key() == b.key() for a, b in zip(c0["_fam"], c["_fam"]))
    bad = test_step_concrete(c)
    print("concrete F at n = N*+{0,1,3,7}, all 33 classes: %d mismatches" % bad); assert bad == 0
    bad = crosscheck(c, 1000, 1000)
    print("brute force a <= b <= 1000: %d mismatches" % bad); assert bad == 0
    c2 = prove_sym((3, 5), (1, 2), 30, [18])
    assert not c2["ok"]; print("negative control u=30 rejected:", c2.get("stage"), c2.get("why"))

    def flip_x(fam):
        f = next(f for f in fam if len(f.X[0]) > 8); X = list(f.X[0]); X[8] ^= 1; f.X[0] = tuple(X)
    def flip_c(fam):
        f = next(f for f in fam if not f.deg); f.C[0] += 1
    def double_y(fam):                   # wall of one class moves 2v per step: slope mismatch
        f = next(f for f in fam if not f.deg); f.Y[0] = f.Y[0] * 2
    def flip_z(fam):                     # tail cell flipped in one visible class
        f = next(f for f in fam if not f.deg)
        n0 = len(f.Z.pre) + len(f.Z.cyc)
        f.Z = Row((1 - f.Z(0),) + tuple(f.Z(t) for t in range(1, n0)), tuple(f.Z(t) for t in range(n0, n0 + len(f.Z.cyc))))
    for mu in (flip_x, flip_c, double_y, flip_z):
        c3 = prove_sym((3, 5), (1, 2), 33, [18], mutate=mu)
        assert not c3["ok"], mu.__name__
        print("mutation %s rejected at %s: %s" % (mu.__name__, c3.get("stage"), c3.get("why")))
    print("PASS (pump_sym: S1={3,5} -> S2={1,2}, u=33, v=18 proved for all a >= %d with the step "
          "symbolic in n; %d affine + %d structural obligations; %.1fs)"
          % (c["a0"], c["obligations_affine"], c["obligations_struct"], time.time() - t))


# ---------------------------------------------------------------- census
def census_job(args):
    S1, S2, u, vs, g = args
    t = time.time()
    try:
        for a0 in (None, 600, 900):
            c = prove_sym(tuple(S1), tuple(S2), u, vs, a0)
            if c["ok"] or c.get("stage") != "infer":
                break
    except Exception as ex:
        return dict(S1=S1, S2=S2, u=u, v=vs, g=g, ok=False, stage="crash", why=repr(ex))
    out = public(c); out["g"] = g
    if c["ok"]:
        out["step_concrete_bad"] = test_step_concrete(c, ns=(0, 2))
        AM = 2000 if c["a0"] >= 500 else 1000
        out["crosscheck_N"] = AM
        out["crosscheck_bad"] = crosscheck(c, AM, AM)
        out["ok"] = out["crosscheck_bad"] == 0 and out["step_concrete_bad"] == 0
    out["sec"] = round(time.time() - t, 1)
    return out


def census(path, outpath, workers=12):
    from multiprocessing import Pool
    C = json.load(open(path))
    jobs = [(c["S1"], S2, c["u"], c["v"], c["g"]) for c in C if c["status"] == "insertion" for S2 in c["S2"]]
    n_ok = 0
    with Pool(workers) as p, open(outpath, "w") as f:
        for r in p.imap_unordered(census_job, jobs):
            f.write(json.dumps(r) + "\n"); f.flush()
            n_ok += r["ok"]
            print(json.dumps({k: r.get(k) for k in ("S1", "S2", "ok", "a0", "Nstar", "max_tau", "stage", "why",
                                                    "crosscheck_bad", "sec")}), flush=True)
    print("census: %d / %d proved" % (n_ok, len(jobs)))


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "--selftest":
        selftest()
    elif a[0] == "--one":
        S1 = tuple(int(x) for x in a[1].split(",")); S2 = tuple(int(x) for x in a[2].split(","))
        u = int(a[3]); vs = [int(x) for x in a[4].split(",")]
        a0 = int(a[5]) if len(a) > 5 else None
        print(json.dumps(public(prove_sym(S1, S2, u, vs, a0))))
    elif a[0] == "--census":
        census(a[1] if len(a) > 1 else "raw/census42.json", a[2] if len(a) > 2 else "raw/out_pump_sym.jsonl")
