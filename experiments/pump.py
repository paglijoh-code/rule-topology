#!/usr/bin/env python3
"""Pumping certificate: PROVES block insertion for two-heap push-subtraction Sub(S1) -push-> Sub(S2).

Rows (lead_a3): row a is d -> outcome(a, a+d), 1 = P.  For a >= M = max S1 (and g purely periodic)
row a is the output of one fixed transducer F reading column d:
    r_a(d) = [g(a) != g(a+d)]  and  for all s in S1:  r_{a-s}(d+s) = 0  and
             (d >= s ? r_a(d-s) = 0 : r_{a-s+d}(s-d) = 0)          (lead_a3.Pair.next_row)
Its state after column d >= M is (r_a(d-M..d-1), d mod per g).

Symbolic family.  For a = a0 + i + n*u (0 <= i < u, n >= 0) we claim
    row a = R_i(n) = X0 . Y1^(n+c1) . X1 . Y2^(n+c2) ... Ym^(n+cm) . Z          (|Yj| = v_j, Z eventually periodic)
with the SAME exponent slope 1 for every class i.  This is "row a+u = row a with v_j cells inserted at wall j".

Proof (all exact, no fitting):
 1. Base: rows a0 .. a0+(N1+1)u-1 computed exactly (lead_a3.Pair) equal the family.
 2. Step: for every class i, feed F the symbolic inputs R_{i-s}(n or n-1) (s in S1). The input columns
    split into  G0 . Q1^(n+e1) . G1 . Q2^(n+e2) ... Qm^(n+em) . Rest  with G_j, Q_j, Rest independent of n
    (all input walls move by v_j per step).  Reading Q_j repeatedly, F's state at block boundaries is
    eventually periodic; we require it to reach a FIXED POINT after tau_j blocks (period 1).  Then for
    every n with n+e_j >= tau_j the output is  out(G0).pre1.W1^(n+e1-tau1).out(G1)... .out(Rest)
    and we check its normal form equals the normal form of R_i(n).  So row a = R_i(n) for all n >= N1.
 3. Induction on a: rows below a0 are exact (finite computation); for a >= a0+N1*u the inputs are earlier
    rows of the family, so the step applies.  Hence the family holds for every a >= a0.  QED (modulo code).

Usage: pump.py --selftest | --one S1 S2 U V[,V2] [A0] | --census [CENSUS_JSON]
"""
import sys, json, os
from math import lcm
from lead_a3 import Pair, Row
from segcert import align


# ---------------------------------------------------------------- eventually periodic helpers
def row_at(Z, t):
    return Z(t)

def row_drop(Z, k):
    """Z shifted left by k (an eventually periodic Row)."""
    if k <= len(Z.pre):
        return Row(Z.pre[k:], Z.cyc)
    j = (k - len(Z.pre)) % len(Z.cyc)
    return Row((), Z.cyc[j:] + Z.cyc[:j])

def row_prepend(w, Z):
    return Row(tuple(w) + Z.pre, Z.cyc)

def row_is_power(Z, Y):
    """Z == Y^infinity ?"""
    v = len(Y)
    n = len(Z.pre) + lcm(len(Z.cyc), v)
    return all(Z(t) == Y[t % v] for t in range(n))


# ---------------------------------------------------------------- symbolic rows
class Sym:
    """X[0] Y[0]^(n+C[0]) X[1] Y[1]^(n+C[1]) ... Y[m-1]^(n+C[m-1]) Z.   deg=True: last wall invisible
    (Z == Y[m-1]^inf); then the row is X[0]...X[m-1] Y[m-1]^inf for every n and C[m-1] is meaningless."""

    def __init__(self, X, Y, C, Z, deg=False):
        self.X = [tuple(x) for x in X]; self.Y = [tuple(y) for y in Y]; self.C = list(C); self.Z = Z
        self.deg = deg          # last wall invisible: Z == Y[-1]^inf, exponent of last run irrelevant

    @property
    def m(self):
        return len(self.Y)

    def concrete(self, n):
        w = []
        if self.deg:
            for j in range(self.m - 1):
                w += list(self.X[j]) + list(self.Y[j]) * (n + self.C[j])
            w += list(self.X[-1])
            return Row(tuple(w), self.Y[-1])
        for j in range(self.m):
            assert n + self.C[j] >= 0, ("negative exponent", n, self.C)
            w += list(self.X[j]) + list(self.Y[j]) * (n + self.C[j])
        return Row(tuple(w) + self.Z.pre, self.Z.cyc)

    def runs(self, delta, s):
        """Affine (const, slope) of start/end of each run in stream coordinates d, for the row taken at
        period index n - delta and read at d + s.  Returns [(a0, aslope, b0, bslope)], zstart."""
        out = []; pos0 = 0; slope = 0
        for j in range(self.m):
            pos0 += len(self.X[j])
            a = (pos0 - s, slope)
            v = len(self.Y[j])
            if self.deg and j == self.m - 1:
                pos0 += 10 ** 9 * v; slope += v      # the run never ends; any end beyond the others is valid
            else:
                pos0 += (self.C[j] - delta) * v; slope += v
            out.append((a[0], a[1], pos0 - s, slope))
        return out, (pos0 - s, slope)

    def normalize(self):
        X, Y, C, Z = [list(x) for x in self.X], [list(y) for y in self.Y], list(self.C), self.Z
        m = len(Y)
        if self.deg:
            C[-1] = 0; Z = Row((), tuple(Y[-1]))
        changed = True
        while changed:
            changed = False
            for j in range(m):
                v = len(Y[j])
                # rotate back: X_j ends with Y_j[-1]
                while X[j] and X[j][-1] == Y[j][-1]:
                    c = X[j].pop(); Y[j] = [c] + Y[j][:-1]
                    if j + 1 < m:
                        X[j + 1] = [c] + X[j + 1]
                    else:
                        Z = row_prepend([c], Z)
                    changed = True
                # absorb forward: what follows starts with Y_j
                if j + 1 < m:
                    while len(X[j + 1]) >= v and X[j + 1][:v] == Y[j]:
                        X[j + 1] = X[j + 1][v:]; C[j] += 1; changed = True
                else:
                    if row_is_power(Z, Y[j]):
                        while X[j] and X[j][-1] == Y[j][-1]:
                            c = X[j].pop(); Y[j] = [c] + Y[j][:-1]
                        return Sym(X, Y, C[:-1] + [None], Row((), tuple(Y[j])), True), True
                    while all(Z(t) == Y[j][t] for t in range(v)):
                        Z = row_drop(Z, v); C[j] += 1; changed = True
        return Sym(X, Y, C, Z), False

    def key(self):
        S, deg = self.normalize()
        return (tuple(S.X), tuple(S.Y), tuple(S.C), S.Z.key, deg)


# ---------------------------------------------------------------- inference of the family
def infer(A, B, vs):
    """Sym R with R(0) = A, R(1) = B, walls of sizes vs (from segcert.align)."""
    M = 6
    if A.key == B.key and len(vs) == 1 and vs[0] % len(A.cyc) == 0:
        # invisible wall: A = pre . cyc^inf, cyc | v
        Y = tuple(A.cyc) * (vs[0] // len(A.cyc))
        return Sym([A.pre], [Y], [0], Row((), Y), deg=True), None
    ins = align(A, B, M, max(vs) + 10, 4 * M + 8)
    if ins is None:
        return None, "align failed"
    if [v for _, v in ins] != list(vs):
        return None, "walls %s != %s" % ([v for _, v in ins], vs)
    X, Y, C = [], [], []
    prev = 0
    for x, v in ins:
        # maximal lag-v run ending at x (inside [prev, x))
        y = x
        while y - 1 - v >= prev and A(y - 1) == A(y - 1 - v):
            y -= 1
        start = y - v                    # A is lag-v periodic on [start, x)
        k = max(0, (x - start) // v)
        if k < 1:
            return None, "no run before wall at %d" % x
        rs = x - k * v
        X.append(tuple(A(t) for t in range(prev, rs)))
        Y.append(tuple(A(t) for t in range(x - v, x)))
        C.append(k)
        prev = x
    Z = row_drop(A, prev)
    R = Sym(X, Y, C, Z)
    if R.concrete(0).key != A.key or R.concrete(1).key != B.key:
        return None, "insertion is not a tandem duplicate (run period does not divide v)"
    return R, None


# ---------------------------------------------------------------- the transducer
class Step:
    """Symbolic F for one class i.  ins[s] = (Sym, delta): input row a-s is R(n-delta)."""

    def __init__(self, P, i_rep_a, ins, near):
        self.P, self.S1, self.M = P, P.S1, P.M
        self.ga = P.gval(i_rep_a)          # g(a), a = a_rep; g(a+d) via gcol(d)
        self.arep = i_rep_a
        self.ins = ins                      # {s: (Sym, delta)}
        self.near = near                    # {k: (Sym, delta)} row a-k, k = 1..M (near-diagonal)

    def gdiff(self, col):
        return self.ga != self.P.gval(self.arep + col)

    def cell(self, state, col, inp):
        """state = r(col-M..col-1); inp[s] = r_{a-s}(col+s); valid for col >= M."""
        if not self.gdiff(col):
            return 0
        for s in self.S1:
            if inp[s] == 1 or state[self.M - s] == 1:
                return 0
        return 1


def prove_case(S1, S2, u, vs, a0=None, base_extra=2, mutate=None):
    """Returns dict with ok, details, and on failure where the induction breaks."""
    P = Pair(S1, S2)
    M, gp = P.M, P.gper
    res = dict(S1=list(S1), S2=list(S2), u=u, v=list(vs))
    if P.gpre != 0:
        return dict(res, ok=False, why="g not purely periodic")
    if u % gp or any(v % gp for v in vs):
        return dict(res, ok=False, why="per(g) does not divide u and v")
    if a0 is None:
        a0 = max(4 * u, 300)
    m = len(vs)
    # rows needed: a0 .. a0 + 3u (inference) plus base
    NEED = a0 + 3 * u + M
    while len(P.rows) < NEED:
        P.next_row()
    fam = []
    for i in range(u):
        R, err = infer(P.rows[a0 + i], P.rows[a0 + i + u], vs)
        if R is None:
            return dict(res, ok=False, a0=a0, stage="infer", cls=i, why=err)
        if R.concrete(2).key != P.rows[a0 + i + 2 * u].key:
            return dict(res, ok=False, a0=a0, stage="infer", cls=i, why="row a0+i+2u breaks the family")
        fam.append(R)
    if mutate:
        mutate(fam)          # test hook: a wrong family must be rejected by the step or the base

    # ---------------- symbolic step for each class
    Nvalid = 1
    taus = []
    for i in range(u):
        ins = {}
        for s in S1:
            j = i - s
            ins[s] = (fam[j % u], 0 if j >= 0 else 1)
        near = {}
        for k in range(1, M + 1):
            j = i - k
            near[k] = (fam[j % u], 0 if j >= 0 else 1)
        # walls of the input streams (affine in n): need equal slopes
        A = [None] * m; B = [None] * m; Zs = []
        for s in S1:
            R, dl = ins[s]
            if R.m != m:
                return dict(res, ok=False, a0=a0, stage="step", cls=i, why="input row with %d walls" % R.m)
            rr, zst = R.runs(dl, s)
            for j, (a_, asl, b_, bsl) in enumerate(rr):
                A[j] = a_ if A[j] is None else max(A[j], a_)
                B[j] = b_ if B[j] is None else min(B[j], b_)
            Zs.append(zst)
        A[0] = max(A[0], M)                 # near-diagonal columns stay in G0
        Vcum = [sum(vs[:j]) for j in range(m + 1)]
        e = [(B[j] - A[j]) // vs[j] for j in range(m)]
        # gap j (after run j) : start A_j + e_j v_j + n V_{j+1}, length A_{j+1} - A_j - e_j v_j
        for j in range(m - 1):
            if A[j + 1] - A[j] - e[j] * vs[j] < 0:
                return dict(res, ok=False, a0=a0, stage="step", cls=i, why="runs overlap")
        # n at which to evaluate n-independent contents: large enough for every exponent >= 2
        nref = 2 + max([2] + [-(R.C[j] - dl) for s, (R, dl) in list(ins.items()) + list(near.items())
                              for j in range(R.m)] + [-ej for ej in e])
        nref += 2
        arep = a0 + i + nref * u
        st = Step(P, arep, ins, near)

        def val(s, col, n):
            R, dl = ins[s]
            return R.concrete(n - dl)(col + s)
        conc = {}
        def crow(R, dl, n):
            k = (id(R), dl, n)
            if k not in conc:
                conc[k] = R.concrete(n - dl)
            return conc[k]

        def stream(s, col, n):
            R, dl = ins[s]
            return crow(R, dl, n)(col + s)

        def run_cols(n, check_n2=True):
            """Run F at period index n through G0, Q-iterations and gaps; return symbolic pieces."""
            out_pieces = []
            # G0 concretely with the near-diagonal rule
            r = []
            for d in range(A[0]):
                if not st.gdiff(d):
                    r.append(0); continue
                c = 1
                for s in S1:
                    if stream(s, d, n) == 1:
                        c = 0; break
                    if d >= s:
                        if r[d - s] == 1:
                            c = 0; break
                    else:
                        R, dl = near[s - d]
                        if crow(R, dl, n)(s - d) == 1:
                            c = 0; break
                r.append(c)
            state = tuple(r[-M:])
            X = [tuple(r)]; Y = []; C = []; tau_l = []
            for j in range(m):
                q0 = A[j] + n * Vcum[j]
                v = vs[j]
                seen = {}; outs = []; sts = []
                while state not in seen:
                    seen[state] = len(sts); sts.append(state)
                    w = []
                    for t in range(v):
                        col = q0 + len(outs) * v + t
                        inp = {s: stream(s, col, n) for s in S1}
                        b = st.cell(state, col, inp)
                        w.append(b); state = state[1:] + (b,)
                    outs.append(tuple(w))
                tau = seen[state]; per = len(sts) - tau
                if n + e[j] < len(sts):
                    return None, dict(stage="step", cls=i, wall=j, why="nref too small for Q-iteration")
                if per != 1:
                    return None, dict(stage="step", cls=i, wall=j,
                                      why="block-boundary state cycles with period %d (tau=%d), not 1" % (per, tau))
                X[-1] = X[-1] + tuple(x for w in outs[:tau] for x in w)
                Y.append(outs[tau]); C.append(e[j] - tau); tau_l.append(tau)
                # columns after the Q-region of wall j are read from the fixed-point state
                gstart = A[j] + e[j] * v + n * Vcum[j + 1]
                state = sts[tau]
                if j + 1 < m:
                    glen = A[j + 1] - A[j] - e[j] * v
                    w = []
                    for t in range(glen):
                        col = gstart + t
                        inp = {s: stream(s, col, n) for s in S1}
                        b = st.cell(state, col, inp); w.append(b); state = state[1:] + (b,)
                    X.append(tuple(w))
                else:
                    # Rest: eventually periodic inputs
                    ins_rows = {}
                    for s in S1:
                        R, dl = ins[s]
                        cr = crow(R, dl, n)
                        ins_rows[s] = row_drop(cr, gstart + s)
                    D0 = max(len(x.pre) for x in ins_rows.values()) + M
                    L = lcm(*[len(x.cyc) for x in ins_rows.values()], gp)
                    seen2 = {}; w = []; t = 0
                    while True:
                        if t >= D0:
                            key = (state, t % L)
                            if key in seen2:
                                jj = seen2[key]; Z = Row(tuple(w[:jj]), tuple(w[jj:t])); break
                            seen2[key] = t
                        col = gstart + t
                        inp = {s: ins_rows[s](t) for s in S1}
                        b = st.cell(state, col, inp); w.append(b); state = state[1:] + (b,); t += 1
            return Sym(X, Y, C, Z), dict(tau=tau_l)

        out, info = run_cols(nref)
        if out is None:
            return dict(res, ok=False, a0=a0, **info)
        out2, info2 = run_cols(nref + 1)
        # structural n-independence sanity: both evaluations give the same symbolic object
        if out2 is None or out.key() != out2.key():
            return dict(res, ok=False, a0=a0, stage="step", cls=i, why="symbolic output depends on n (bug or too small nref)")
        if out.key() != fam[i].key():
            # where does it break?  compare concretely at nref
            ca, cb = out.concrete(nref), fam[i].concrete(nref)
            dpos = next((t for t in range(len(ca.pre) + len(cb.pre) + lcm(len(ca.cyc), len(cb.cyc)) + 5)
                         if ca(t) != cb(t)), None)
            return dict(res, ok=False, a0=a0, stage="step", cls=i,
                        why="F(family) != family (first differing column %s at n=%d)" % (dpos, nref))
        # validity range: every exponent in inputs >= 1, every Q-region has n+e_j >= tau_j + 1
        Nvalid = max(Nvalid, nref)
        taus.append(info["tau"])

    # ---------------- base: concrete rows a0 .. a0 + (Nvalid+1)u + M match the family
    NB = a0 + (Nvalid + base_extra) * u + M
    while len(P.rows) < NB:
        P.next_row()
    for a in range(a0, NB):
        i, n = (a - a0) % u, (a - a0) // u
        if fam[i].concrete(n).key != P.rows[a].key:
            return dict(res, ok=False, a0=a0, stage="base", row=a, why="concrete row differs from family")
    return dict(res, ok=True, a0=a0, N1=Nvalid, base_rows=[a0, NB], max_tau=max(max(t) for t in taus),
                walls=[[list(f.Y[j]).__len__() for j in range(f.m)] for f in fam[:1]],
                _P=P, _fam=fam)


def family_row(cert, a):
    a0, u = cert["a0"], cert["u"]
    if a < a0:
        return cert["_P"].rows[a]
    return cert["_fam"][(a - a0) % u].concrete((a - a0) // u)


def crosscheck(cert, AMAX=1000, N=1000):
    """Every symbolic row a <= AMAX against brute force solve2 (cells a <= b <= N) and lead_a3 rows."""
    from lead_a2 import solve2
    S1, S2 = cert["S1"], cert["S2"]
    B = solve2(set(S1), set(S2), N)
    P2 = Pair(S1, S2)
    bad = 0
    for a in range(cert["a0"], AMAX + 1):
        R = family_row(cert, a)
        while len(P2.rows) <= a:
            P2.next_row()
        if R.key != P2.rows[a].key:
            bad += 1
        for b in range(a, N + 1):
            if R(b - a) != B[a][b]:
                bad += 1
    return bad


def public(c):
    return {k: v for k, v in c.items() if not k.startswith("_")}


def selftest():
    c = prove_case((3, 5), (1, 2), 33, [18])
    print(json.dumps(public(c)))
    assert c["ok"], c
    bad = crosscheck(c, 1000, 1000)
    print("crosscheck a<=1000 mismatches:", bad)
    assert bad == 0
    # a negative control: wrong u must not prove
    c2 = prove_case((3, 5), (1, 2), 30, [18])
    assert not c2["ok"], "negative control proved?!"
    print("negative control (u=30) rejected:", c2.get("stage"), c2.get("why"))
    def flip_x(fam):            # one cell of one class's head flipped
        f = next(f for f in fam if len(f.X[0]) > 8); X = list(f.X[0]); X[8] ^= 1; f.X[0] = tuple(X)
    def flip_c(fam):            # one class's wall one block late
        f = next(f for f in fam if not f.deg); f.C[0] += 1
    for mu in (flip_x, flip_c):
        c3 = prove_case((3, 5), (1, 2), 33, [18], mutate=mu)
        assert not c3["ok"], mu.__name__
        print("mutation %s rejected at %s: %s" % (mu.__name__, c3.get("stage"), c3.get("why")))
    print("PASS (S1={3,5} -> S2={1,2}: block insertion u=33, v=18 PROVED for all a >= a0; brute force agrees for a <= 1000)")


def census_job(args):
    S1, S2, u, vs, g = args
    import time
    t = time.time()
    try:
        for a0 in (None, 600, 900):          # the wall must be visible in every class at a0; retry later
            c = prove_case(tuple(S1), tuple(S2), u, vs, a0)
            if c["ok"] or c.get("stage") != "infer":
                break
    except Exception as ex:          # report, never hide
        return dict(S1=S1, S2=S2, u=u, v=vs, g=g, ok=False, stage="crash", why=repr(ex))
    out = public(c); out["g"] = g
    if c["ok"]:
        out["crosscheck_bad"] = crosscheck(c, 1000, 1000)
        out["ok"] = out["crosscheck_bad"] == 0
    out["sec"] = round(time.time() - t, 1)
    return out


def census(path, workers=8):
    from multiprocessing import Pool
    C = json.load(open(path))
    jobs = [(c["S1"], S2, c["u"], c["v"], c["g"]) for c in C if c["status"] == "insertion" for S2 in c["S2"]]
    with Pool(workers) as p:
        for r in p.imap_unordered(census_job, jobs):
            print(json.dumps(r), flush=True)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "--selftest":
        selftest()
    elif a[0] == "--one":
        S1 = tuple(int(x) for x in a[1].split(",")); S2 = tuple(int(x) for x in a[2].split(","))
        u = int(a[3]); vs = [int(x) for x in a[4].split(",")]
        a0 = int(a[5]) if len(a) > 5 else None
        c = prove_case(S1, S2, u, vs, a0)
        print(json.dumps(public(c)))
        if c["ok"] and "--cross" in a:
            print("crosscheck mismatches:", crosscheck(c))
    elif a[0] == "--census":
        census(a[1] if len(a) > 1 else os.path.join(os.environ.get("TMPDIR", "/tmp"), "census.json"))
