#!/usr/bin/env python3
"""sqrtwall: a computer proof of the sqrt(a) wall law for S1 = {1,2,5,6}, g = 01234
(S2 = [1,2,3,4] or [1,2,3,4,6]).  

Rows (lead_a3): row a is d -> outcome(a, a+d), 1 = P.  For a >= 6 row a is determined by rows a-1..a-6:
    r_a(d) = 1  iff  d % 5 != 0  and for every s in S1:  r_{a-s}(d+s) = 0  and
                     (d >= s ? r_a(d-s) = 0 : r_{a-(s-d)}(s-d) = 0)            (RULE; lead_a3.Pair.next_row)
(g = 01234 has period 5 and no preperiod, so g(a) != g(a+d) iff d % 5 != 0: the rule does not depend on a.)

Two-parameter family.  t_k = 7k^2 + 35k + 13, gap_k = t_{k+1} - t_k = 14k + 42.  Write k = 7q + kap
(kap in 0..6) and a = t_k + r, 0 <= r < gap_k = 98q + 14 kap + 42.  For each kap the r-range is cut into
PIECES; a piece has rows r = b0 + b1*q + i + P*j with class i in [0, P) and j in [0, c0 + c1*q).  Each
class has one symbolic row
    F0 . W1^e1 . F1 . W2^e2 ... Fm . cyc^inf          e_x = c + a*q + b*j   (affine exponents)
Pieces: A (after the jump), L (glider moving left: P = 42, 35 cells per 42 rows), M (reflection at the
diagonal), R (moving right: P = 7, 35 cells per 7 rows), E (arrival at the wall and the jump).

Proof.
 1. STEP (symbolic, verify_class): for every class and every (q, j) in its domain with q >= Q0+1, the
    claimed row satisfies RULE at EVERY cell d >= 0, where rows a-1..a-6 are the claimed family rows
    (same piece, previous piece, or the previous k: the jump k-1 -> k, incl. kap 0 <- kap 6 at q-1).
    The check is local consistency, not simulation: all 9 views (self at d and d-s, inputs at d+s) are
    cut at the union of their breakpoints (affine in q, j; ordered on the whole domain by a vertex/ray
    test); between two breakpoints every view is inside one fixed word (then the interval has constant
    length and is checked cell by cell) or inside one periodic run (then RULE is checked on a full
    common period, with all phases shown to be independent of q and j).
 2. BASE: every row with q = Q0 (k = 7 Q0 .. 7 Q0 + 6) equals the exact row (lead_a3.Pair).
 3. Induction on a: RULE determines row a from rows a-1..a-6, so family = true rows for all a >= t_{7 Q0}.
 Cross-check: C brute force bf2.c for both S2, every cell a <= b <= N.
The inference of the family (decomposition into period-35 runs) is NOT trusted; only steps 1-2 are.

Usage: sqrtwall.py --prove [NBF] | --selftest | --far [N] | --show KAP
"""
import sys, os, json, time, pickle
from math import lcm
from functools import cmp_to_key
from lead_a3 import Pair, Row

S1 = (1, 2, 5, 6)
S2S = ((1, 2, 3, 4), (1, 2, 3, 4, 6))
M = 6
PER = 35            # background period in d
TH = 75             # a period-35 run must be at least this long to be a run (inference only)
QI = 5              # inference samples at q = QI, QI+1 (checked at QI+2)
Q0 = 3              # the family is claimed for q >= Q0 (k >= 21)
HERE = os.path.dirname(os.path.abspath(__file__))
TMP = os.environ.get("PUMP2_TMP", os.environ.get("TMPDIR", "/tmp"))


def tk(k, t0=13):
    return 7 * k * k + 35 * k + t0


class Fail(Exception):
    pass


# ---------------------------------------------------------------- exact rows
_ROWS = None


def exact_rows(N):
    """Exact rows 0..N-1 (lead_a3.Pair).  Same rows for both S2 (asserted: same g)."""
    global _ROWS
    if _ROWS is not None and len(_ROWS) >= N:
        return _ROWS
    for S2 in S2S:
        P = Pair(S1, S2)
        assert P.gpre == 0 and P.gper == 5 and list(P.g[:5]) == [0, 1, 2, 3, 4], "g is not 01234"
    f = os.path.join(TMP, "sqrtwall_rows_%d.pkl" % N)
    if os.path.exists(f) and os.path.getmtime(f) > os.path.getmtime(os.path.join(HERE, "lead_a3.py")):
        _ROWS = [Row(p, c) for p, c in pickle.load(open(f, "rb"))]
        return _ROWS
    P = Pair(S1, S2S[0])
    while len(P.rows) < N:
        P.next_row()
    pickle.dump([r.key for r in P.rows], open(f, "wb"))
    _ROWS = P.rows
    return _ROWS


# ---------------------------------------------------------------- affine forms c + a*q + b*j
def fadd(x, y): return (x[0] + y[0], x[1] + y[1], x[2] + y[2])
def fsub(x, y): return (x[0] - y[0], x[1] - y[1], x[2] - y[2])
def fmul(x, n): return (x[0] * n, x[1] * n, x[2] * n)
def fev(x, q, j): return x[0] + x[1] * q + x[2] * j
def fconst(c): return (c, 0, 0)


class Dom:
    """conv(verts) + cone(rays) in the (q, j) plane; contains every integer parameter point of a case."""

    def __init__(self, verts, rays, jf=None):
        self.verts, self.rays, self.jf = verts, rays, jf     # jf: on this domain j = jf0 + jf1*q exactly

    def nonneg(self, f):
        return all(fev(f, q, j) >= 0 for q, j in self.verts) and \
            all(f[1] * dq + f[2] * dj >= 0 for dq, dj in self.rays)


# ---------------------------------------------------------------- symbolic rows
class SymRow:
    """segs: ('F', word) or ('R', W, form); then cyc^inf."""

    def __init__(self, segs, cyc):
        self.segs, self.cyc = segs, tuple(cyc)

    def concrete(self, q, j):
        w = []
        for s in self.segs:
            if s[0] == 'F':
                w += s[1]
            else:
                e = fev(s[2], q, j)
                if e < 0:
                    return None
                w += list(s[1]) * e
        return Row(w, self.cyc)

    def subst(self, delta, jf):
        """Same row with q -> q - delta, j -> jf(q, j)."""
        out = []
        for s in self.segs:
            if s[0] == 'F':
                out.append(s)
            else:
                c, a, b = s[2]
                out.append(('R', s[1], (c - a * delta + b * jf[0], a + b * jf[1], b * jf[2])))
        return SymRow(out, self.cyc)

    def layout(self):
        """[(kind, word, start, end)]; the last entry is the tail ('R', cyc, start, None)."""
        out, pos = [], (0, 0, 0)
        for s in self.segs:
            if s[0] == 'F':
                if not s[1]:
                    continue
                end = fadd(pos, fconst(len(s[1])))
            else:
                end = fadd(pos, fmul(s[2], len(s[1])))
            out.append((s[0], s[1], pos, end)); pos = end
        out.append(('R', self.cyc, pos, None))
        return out

    def prelen(self):
        return self.layout()[-1][2]


def decompose(row):
    """Skeleton of a concrete row: fixed words and maximal lag-PER runs (length >= TH), left to right.
    Returns (signature, exponents)."""
    x = list(row.pre); n = len(x)
    runs = []; t = PER
    while t < n:
        if x[t] == x[t - PER]:
            e = t
            while e < n and x[e] == x[e - PER]:
                e += 1
            if e - t + PER >= TH:
                runs.append((t - PER, e))
            t = e
        else:
            t += 1
    sig, exps, prev = [], [], 0
    for s, e in runs:
        s = max(s, prev)
        k = (e - s) // PER
        if k < 1:
            continue
        sig.append(tuple(x[prev:s])); sig.append(tuple(x[s:s + PER])); exps.append(k)
        prev = s + PER * k
    sig.append(tuple(x[prev:]))
    return (tuple(sig), row.cyc), exps


def infer(sample, q1, j1, two):
    """SymRow from samples (q1, j1), (q1+1, j1) and, if two, (q1, j1+1).  None if the skeletons differ."""
    A, B = sample(q1, j1), sample(q1 + 1, j1)
    C = sample(q1, j1 + 1) if two else A
    if A is None or B is None or C is None:
        return None
    (sa, ea), (sb, eb), (sc, ec) = decompose(A), decompose(B), decompose(C)
    if sa != sb or sa != sc:
        return None
    sig, cyc = sa
    segs = []
    for x in range(len(ea)):
        a = eb[x] - ea[x]; b = ec[x] - ea[x]
        segs.append(('F', sig[2 * x])); segs.append(('R', sig[2 * x + 1], (ea[x] - a * q1 - b * j1, a, b)))
    segs.append(('F', sig[-1]))
    return SymRow(segs, cyc)


# ---------------------------------------------------------------- the family
class Piece:
    def __init__(self, name, base, P, cnt, cls):
        self.name, self.base, self.P, self.cnt, self.cls = name, base, P, cnt, cls   # base, cnt: (c0, c1) in q

    def end(self):
        return (self.base[0] + self.P * self.cnt[0], self.base[1] + self.P * self.cnt[1])


class Family:
    def __init__(self, pieces, q0=Q0, t0=13):
        self.pieces, self.q0, self.t0 = pieces, q0, t0       # pieces[kap] = [Piece]

    def gap(self, kap):
        return self.pieces[kap][-1].end()

    def locate(self, a):
        k = 0
        while tk(k + 1, self.t0) <= a:
            k += 1
        return k % 7, k // 7, a - tk(k, self.t0)

    def row(self, a):
        kap, q, r = self.locate(a)
        if q < self.q0:
            return None
        for p in self.pieces[kap]:
            b = p.base[0] + p.base[1] * q
            n = p.cnt[0] + p.cnt[1] * q
            if b <= r < b + p.P * n:
                return p.cls[(r - b) % p.P].concrete(q, (r - b) // p.P)
        return None

    def a_start(self):
        return tk(7 * self.q0, self.t0)


def build_family(rows, mlo=1, mhi=1, verbose=False):
    """Infer the pieces from exact rows (q = QI..QI+2).  Untrusted: the step and the base judge it."""
    def Rw(kap, q, r):
        k = 7 * q + kap
        if r < 0 or r >= 14 * k + 42 or tk(k) + r >= len(rows):
            return None
        return rows[tk(k) + r]
    QS = (QI, QI + 1, QI + 2)
    fam = []
    for kap in range(7):
        # ---- L classes on absolute r = i + 42 j
        Lc = []
        for i in range(42):
            S = infer(lambda q, j: Rw(kap, q, i + 42 * j), QI, QI, True)
            if S is None:
                raise Fail("L inference failed kap=%d i=%d" % (kap, i))
            Lc.append(S)
        Rc = []
        jm = QI + 6 + (13 * kap) // 7
        for i in range(7):
            S = infer(lambda q, j: Rw(kap, q, 84 * q + i + 7 * j), QI, jm, True)
            if S is None:
                raise Fail("R inference failed kap=%d i=%d" % (kap, i))
            Rc.append(S)

        def okL(q, r):
            c = Lc[r % 42].concrete(q, r // 42)
            return c is not None and c.key == Rw(kap, q, r).key

        def okR(q, r):
            o = r - 84 * q
            if o < 0:
                return False
            c = Rc[o % 7].concrete(q, o // 7)
            return c is not None and c.key == Rw(kap, q, r).key
        aL, eL, aR, eR = [], [], [], []
        for q in QS:
            gap = 98 * q + 14 * kap + 42
            mid = 42 * q
            if not okL(q, mid):
                raise Fail("L mid row invalid kap=%d q=%d" % (kap, q))
            lo = mid
            while lo > 0 and okL(q, lo - 1):
                lo -= 1
            hi = mid
            while hi < gap and okL(q, hi):
                hi += 1
            aL.append(lo); eL.append(hi - 84 * q)
            mid = 84 * q + 7 * jm + 7 * (q - QI)
            if not okR(q, mid):
                raise Fail("R mid row invalid kap=%d q=%d" % (kap, q))
            lo = mid
            while lo > 0 and okR(q, lo - 1):
                lo -= 1
            hi = mid
            while hi < gap and okR(q, hi):
                hi += 1
            aR.append(lo - 84 * q); eR.append(hi - 98 * q)
        if verbose:
            print("kap", kap, "L valid from", aL, "to 84q+", eL, "| R valid from 84q+", aR, "to 98q+", eR, flush=True)
        bL = max(aL) + mlo
        cL = (min(eL) - mhi - bL) // 42            # cnt_L = 2q + cL
        endL = bL + 42 * cL                         # + 84 q
        bR = max(max(aR) + mlo, endL)               # + 84 q
        cR = (min(eR) - mhi - bR) // 7              # cnt_R = 2q + cR
        endR = bR + 7 * cR                          # + 98 q
        gap0 = 14 * kap + 42

        def const_piece(name, b0, b1, n):
            cls = []
            for i in range(n):
                S = infer(lambda q, j: Rw(kap, q, b0 + b1 * q + i), QI, 0, False)
                if S is None:
                    raise Fail("%s inference failed kap=%d row %d+%dq" % (name, kap, b0 + i, b1))
                cls.append(S)
            return Piece(name, (b0, b1), n, (1, 0), cls)
        ps = []
        if bL > 0:
            ps.append(const_piece("A", 0, 0, bL))
        ps.append(Piece("L", (bL, 0), 42, (cL, 2),
                        [Lc[(bL + i) % 42].subst(0, ((bL + i) // 42, 0, 1)) for i in range(42)]))
        if bR > endL:
            ps.append(const_piece("M", endL, 84, bR - endL))
        ps.append(Piece("R", (bR, 84), 7, (cR, 2),
                        [Rc[(bR + i) % 7].subst(0, ((bR + i) // 7, 0, 1)) for i in range(7)]))
        if gap0 > endR:
            ps.append(const_piece("E", endR, 98, gap0 - endR))
        fam.append(ps)
    return Family(fam)


# ---------------------------------------------------------------- the symbolic step
def resolve(F, kap, rf, D):
    """The family row at r = rf(q, j) of class kap (r < 0: the previous k), as a SymRow in (q, j)."""
    delta = 0
    if not D.nonneg(rf):
        if not D.nonneg(fsub(fconst(-1), rf)):
            raise Fail("row index changes sign on the domain")
        kap = (kap - 1) % 7
        if kap == 6:
            delta = 1
        g0, g1 = F.gap(kap)
        rf = fadd(rf, (g0 - g1 * delta, g1, 0))
        if not D.nonneg(rf):
            raise Fail("row index more than one k back")
    for p in F.pieces[kap]:
        base = (p.base[0] - p.base[1] * delta, p.base[1], 0)
        e0, e1 = p.end()
        end = (e0 - e1 * delta, e1, 0)
        off = fsub(rf, base)
        if D.nonneg(off) and D.nonneg(fsub(fsub(end, rf), fconst(1))):
            if off[1] % p.P or off[2] % p.P:
                raise Fail("class of the input row depends on q or j")
            i = off[0] % p.P
            return p.cls[i].subst(delta, ((off[0] - i) // p.P, off[1] // p.P, off[2] // p.P))
    raise Fail("input row is not inside one piece on the whole domain")


def read_const(lay, pos, D):
    for kind, w, st, en in lay:
        off = fsub(fconst(pos), st)
        if D.nonneg(off) and (en is None or D.nonneg(fsub(fsub(en, fconst(pos)), fconst(1)))):
            if kind == 'F':
                if off[1] or off[2]:
                    raise Fail("head read at a moving offset")
                return w[off[0]]
            p = len(w)
            if off[1] % p or off[2] % p:
                raise Fail("head read at a moving phase")
            return w[off[0] % p]
    raise Fail("head read not inside one segment")


def rule(d5, ins, selfprev):
    if d5 == 0:
        return 0
    return 0 if (1 in ins or 1 in selfprev) else 1


def verify_on(F, kap, p, i, D):
    """RULE at every cell of the claimed row (kap, piece p, class i), for every (q, j) in D.  Raises Fail."""
    me = p.cls[i]
    rf = (p.base[0] + i, p.base[1], p.P)
    if D.jf is not None:                                    # j is a function of q here: eliminate it
        me = me.subst(0, D.jf)
        rf = (rf[0] + rf[2] * D.jf[0], rf[1] + rf[2] * D.jf[1], 0)
    for s in me.segs:
        if s[0] == 'R' and not D.nonneg(s[2]):
            raise Fail("negative exponent in the claimed row")
    inp = {s: resolve(F, kap, fsub(rf, fconst(s)), D) for s in range(1, M + 1)}
    for s in inp:
        for g in inp[s].segs:
            if g[0] == 'R' and not D.nonneg(g[2]):
                raise Fail("negative exponent in an input row")
    lme = me.layout(); lin = {s: inp[s].layout() for s in inp}
    # head: d < M, all reads at constant positions
    for d in range(M):
        ins = [read_const(lin[s], d + s, D) for s in S1]
        sp = [read_const(lme, d - s, D) if d >= s else read_const(lin[s - d], s - d, D) for s in S1]
        if read_const(lme, d, D) != rule(d % 5, ins, sp):
            raise Fail("RULE fails at d=%d" % d)
    # views: (layout, shift): value at d is row(d + shift)
    views = [(lme, 0)] + [(lme, -s) for s in S1] + [(lin[s], s) for s in S1]
    bps = {fconst(M)}
    for lay, sh in views:
        for kind, w, st, en in lay:
            bps.add(fsub(st, fconst(sh)))

    def cmp(x, y):
        if x == y:
            return 0
        if D.nonneg(fsub(y, x)):
            return -1
        if D.nonneg(fsub(x, y)):
            return 1
        raise Fail("breakpoints %s, %s not ordered on the domain" % (x, y))
    bl = sorted(bps, key=cmp_to_key(cmp))
    for x in range(len(bl) - 1):
        if not D.nonneg(fsub(bl[x + 1], bl[x])):
            raise Fail("breakpoints not ordered on the domain")
    bl = bl[bl.index(fconst(M)):]
    ncell = 0
    for m, B in enumerate(bl):
        Bn = bl[m + 1] if m + 1 < len(bl) else None
        ln = fsub(Bn, B) if Bn is not None else None
        if ln == (0, 0, 0):
            continue
        if B[1] % 5 or B[2] % 5:
            raise Fail("d mod 5 at a breakpoint depends on q or j")
        loc = []
        const = ln is not None and ln[1] == 0 and ln[2] == 0
        L = 5
        for lay, sh in views:
            for kind, w, st, en in lay:
                off = fsub(fadd(B, fconst(sh)), st)
                if D.nonneg(off) and (en is None or (Bn is not None and D.nonneg(fsub(fsub(en, fconst(sh)), Bn)))):
                    break
            else:
                raise Fail("a view is not inside one segment between two breakpoints")
            if kind == 'F':
                if not const or off[1] or off[2]:
                    raise Fail("fixed word under a moving interval")
                loc.append((w, off[0], 0))
            else:
                pp = len(w)
                if off[1] % pp or off[2] % pp:
                    raise Fail("phase of a run depends on q or j")
                loc.append((w, off[0] % pp, pp)); L = lcm(L, pp)
        n = ln[0] if const else L
        for t in range(n):
            v = [w[(o + t) % pp] if pp else w[o + t] for w, o, pp in loc]
            if v[0] != rule((B[0] + t) % 5, v[5:], v[1:5]):
                raise Fail("RULE fails at d = %s + %d" % (B, t))
        ncell += n
    return ncell


def domains(p, Q):
    """Candidate covers of {q >= Q, 0 <= j < cnt(q)} by Doms, coarsest first."""
    c0, c1 = p.cnt
    n = c0 + c1 * Q
    assert n >= 1, "empty piece at q = %d" % Q
    full = Dom([(Q, 0), (Q, n - 1)], [(1, 0), (1, c1)])
    if c1 == 0 and c0 == 1:
        full.jf = (0, 0, 0)
        return [[full]]
    covers = [[full]]
    for K in (1, 2, 3):                                     # the first K and the last K values of j apart
        if n < 2 * K + 1:
            break
        lo = [Dom([(Q, x)], [(1, 0)], (x, 0, 0)) for x in range(K)]
        hi = [Dom([(Q, n - 1 - x)], [(1, c1)], (c0 - 1 - x, c1, 0)) for x in range(K)]
        mid = Dom([(Q, K), (Q, n - 1 - K)], [(1, 0), (1, c1)])
        covers.append(lo + [mid] + hi)
    return covers


def verify_class(F, kap, p, i):
    why = None
    for cover in domains(p, F.q0 + 1):
        try:
            return sum(verify_on(F, kap, p, i, D) for D in cover), None
        except Fail as ex:
            why = str(ex)
    return 0, why


def prove_step(F, stop_first=True):
    nclass = ncell = 0; bad = []
    for kap in range(7):
        for p in F.pieces[kap]:
            for i in range(p.P):
                n, why = verify_class(F, kap, p, i)
                nclass += 1; ncell += n
                if why:
                    bad.append((kap, p.name, i, why))
                    if stop_first:
                        return dict(ok=False, classes=nclass, bad=bad)
    return dict(ok=not bad, classes=nclass, cells=ncell, bad=bad)


def check_base(F, rows, qmax=None):
    """Concrete rows with q = q0 (qmax: up to qmax, as an extra) equal the family."""
    qmax = F.q0 if qmax is None else qmax
    lo, hi = F.a_start(), tk(7 * (qmax + 1), F.t0)
    assert hi <= len(rows)
    for a in range(lo, hi):
        R = F.row(a)
        if R is None or R.key != rows[a].key:
            return dict(ok=False, row=a, why="family row differs from the exact row")
    return dict(ok=True, rows=[lo, hi])


def check_shape(F):
    """The pieces tile [0, gap_k) with gap_k = 98q + 14 kap + 42, for q >= q0."""
    for kap in range(7):
        pos = (0, 0)
        for p in F.pieces[kap]:
            if p.base != pos or p.cnt[0] + p.cnt[1] * F.q0 < 1 or p.cnt[1] < 0:
                return False
            pos = p.end()
        if pos != (14 * kap + 42, 98):
            return False
    return True


def corollary(F):
    """pre(a) - w_k per row class, from the symbolic rows (w_k = 35 + 10k = 35 + 10 kap + 70 q).
    The symbolic prefix length is pre(a) when the prefix is canonical: its last cell (in a fixed word, or
    in a run whose exponent is >= 1 on the whole domain) differs from the cycle's last cell."""
    out = dict(first=set(), body=set(), last3={})
    for kap in range(7):
        gap0 = 14 * kap + 42
        for p in F.pieces[kap]:
            for i, S in enumerate(p.cls):
                D = domains(p, F.q0)[0][0]
                for g in reversed([s for s in S.segs if s[1]]):     # every possible last cell of the prefix
                    assert g[1][-1] != S.cyc[-1], "prefix not canonical"
                    if g[0] == 'F' or D.nonneg(fsub(g[2], fconst(1))):
                        break
                else:
                    raise AssertionError("prefix may be empty")
                assert len(S.cyc) == 10
                dv = fsub(S.prelen(), (35 + 10 * kap, 70, 0))
                assert dv[1] == 0 and dv[2] == 0, "pre - w_k is not constant in a class"
                back = gap0 - (p.base[0] + i) if p.base[1] == 98 else None    # rows before the next jump
                if back is not None and back <= 3:
                    out["last3"].setdefault(kap, [None] * 3)[3 - back] = dv[0]
                else:
                    out["body"].add(dv[0])
                if p.base == (0, 0) and i == 0:
                    out["first"].add(dv[0])
    out["first"] = sorted(out["first"]); out["body"] = sorted(out["body"])
    out["last3"] = sorted(set(map(tuple, out["last3"].values())))
    out["ok"] = out["first"] == [0] and out["body"] == [-20, -15, -10, -5, 0] and out["last3"] == [(5, 10, -5)]
    return out


def check_rule(rows, lo, hi):
    """Trust anchor for RULE: it recomputes the exact rows lo..hi-1 from the six rows before, cell by cell."""
    for a in range(lo, hi):
        me = rows[a]
        for d in range(len(me.pre) + 40):
            ins = [rows[a - s](d + s) for s in S1]
            sp = [me(d - s) if d >= s else rows[a - (s - d)](s - d) for s in S1]
            if me(d) != rule(d % 5, ins, sp):
                return False
    return True


def check_small(rows, kmax):
    """The wall law on the exact rows for k < kmax (the finite part below the family)."""
    for k in range(kmax):
        w, g = 35 + 10 * k, 14 * k + 42
        for r in range(g):
            d = len(rows[tk(k) + r].pre) - w
            if r >= g - 3:
                ok = d == (5, 10, -5)[r - (g - 3)]
            else:
                ok = -20 <= d <= 0 and (r > 0 or d == 0)
            if not ok or len(rows[tk(k) + r].cyc) != 10:
                return False
    return True


def check_far(F, rows, N):
    """Out of sample: family rows equal the exact rows up to N (inference used q = QI..QI+2 only)."""
    return sum(1 for a in range(F.a_start(), N + 1) if F.row(a) is None or F.row(a).key != rows[a].key)


def crosscheck_bf(F, rows, N):
    """Every row a <= N (family rows from a_start on, exact rows below) against bf2.c, both S2."""
    import numpy as np
    from pump2 import bf_matrix, row_arr
    res = {}
    for S2 in S2S:
        B = bf_matrix(S1, S2, N)
        bad = nf = 0
        for a in range(N + 1):
            R = F.row(a) if a >= F.a_start() else rows[a]
            if R is None:
                bad += N - a + 1; continue
            nf += a >= F.a_start()
            bad += int(np.count_nonzero(row_arr(R, N - a + 1) != B[a, a:]))
        res["".join(map(str, S2))] = dict(N=N, family_rows=nf, bad=bad)
    return res


def prove(NBF=22000, verbose=True):
    t = time.time()
    NR = tk(7 * (QI + 3)) + 10
    rows = exact_rows(max(NR, NBF + 1))
    F = build_family(rows, verbose=verbose)
    out = dict(S1=list(S1), S2=[list(s) for s in S2S], q0=F.q0, a_start=F.a_start(),
               pieces={kap: [(p.name, p.base, p.P, p.cnt) for p in F.pieces[kap]] for kap in range(7)})
    out["shape"] = check_shape(F)
    out["rule"] = check_rule(rows, F.a_start(), F.a_start() + 1500)
    st = prove_step(F, stop_first=False)
    out["step"] = dict(ok=st["ok"], classes=st["classes"], cells=st.get("cells"), bad=st["bad"][:8], nbad=len(st["bad"]))
    out["base"] = check_base(F, rows)
    out["base_extra"] = check_base(F, rows, QI + 2)
    out["ok"] = bool(out["shape"] and out["rule"] and st["ok"] and out["base"]["ok"])
    if out["ok"]:
        out["corollary_pre_minus_w"] = corollary(F)
        out["small_k"] = check_small(rows, 7 * F.q0)
        out["ok"] = out["corollary_pre_minus_w"]["ok"] and out["small_k"]
        if NBF:
            out["bf"] = crosscheck_bf(F, rows, NBF)
            out["ok"] = out["ok"] and all(v["bad"] == 0 for v in out["bf"].values())
    out["sec"] = round(time.time() - t, 1)
    return out, F, rows


def selftest():
    import copy
    out, F, rows = prove(NBF=6000, verbose=False)        # small brute force here; --prove uses 22000
    print(json.dumps({k: v for k, v in out.items() if k != "pieces"}))
    assert out["ok"], "proof failed"

    def mutated(f):
        G = copy.deepcopy(F); f(G); return G

    # 1. wrong jump law t_k = 7k^2 + 35k + 14: the step is translation invariant, so the BASE must reject
    G = Family(F.pieces, F.q0, t0=14)
    b = check_base(G, rows)
    assert not b["ok"]; print("control 7k^2+35k+14 rejected by the base at row", b["row"])
    G = Family(F.pieces, F.q0, t0=12)
    b = check_base(G, rows)
    assert not b["ok"]; print("control 7k^2+35k+12 rejected by the base at row", b["row"])

    # 2. gap 14k + 41 for kap = 3 (jump one row early): the STEP must reject
    def early(G):
        p = G.pieces[3][-1]; assert p.name == "E"; p.P -= 1; p.cls.pop()
    G = mutated(early)
    assert not check_shape(G)
    s = prove_step(G); assert not s["ok"]; print("control gap-1 (kap 3) rejected by the step:", s["bad"][0])

    # 3. one cell of one L class flipped; 4. the glider one period late in one L class; 5. same for R
    def flip(G):
        S = next(p for p in G.pieces[2] if p.name == "L").cls[17]
        x = max(range(len(S.segs)), key=lambda x: len(S.segs[x][1]) if S.segs[x][0] == 'F' else -1)
        w = list(S.segs[x][1]); w[len(w) // 2] ^= 1; S.segs[x] = ('F', tuple(w))

    def late(name, c):
        def f(G):
            S = next(p for p in G.pieces[5] if p.name == name).cls[c]
            xs = [x for x in range(len(S.segs)) if S.segs[x][0] == 'R']
            a, b = xs[0], xs[-1]
            S.segs[a] = ('R', S.segs[a][1], fadd(S.segs[a][2], fconst(1)))
            S.segs[b] = ('R', S.segs[b][1], fsub(S.segs[b][2], fconst(1)))
        return f
    for name, f in (("cell flip", flip), ("L glider late", late("L", 20)), ("R glider late", late("R", 3))):
        s = prove_step(mutated(f)); assert not s["ok"], name
        print("control %s rejected by the step: %s" % (name, s["bad"][0]))

    # 6. a wrong exponent slope (wall grows 35 per q in one E class): step rejects
    def slope(G):
        S = G.pieces[0][-1].cls[0]
        x = next(x for x in range(len(S.segs)) if S.segs[x][0] == 'R' and S.segs[x][2][1])
        c, a, b = S.segs[x][2]; S.segs[x] = ('R', S.segs[x][1], (c + 4, a - 1, b))
    s = prove_step(mutated(slope)); assert not s["ok"]
    print("control wrong slope rejected by the step:", s["bad"][0])

    # 7. a corrupted family is caught by the C brute force
    def tailflip(G):
        S = G.pieces[1][0].cls[0]; w = list(S.segs[-1][1]); w[0] ^= 1; S.segs[-1] = ('F', tuple(w))
    G = mutated(tailflip); G.q0 = 0
    Gs = Family(G.pieces, 0)
    bf = crosscheck_bf(Gs, rows, 3000)
    print("bf2 on a corrupted family (q0 = 0, so early rows are missing too):", bf)
    assert all(v["bad"] > 0 for v in bf.values())
    print("PASS")


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a or a[0] == "--selftest":
        selftest()
    elif a[0] == "--prove":
        out, F, rows = prove(int(a[1]) if len(a) > 1 else 22000)
        print(json.dumps(out))
    elif a[0] == "--far":
        N = int(a[1]) if len(a) > 1 else 60000
        rows = exact_rows(N + 1)
        F = build_family(rows[:tk(7 * (QI + 3)) + 10])
        print(json.dumps(dict(N=N, a_start=F.a_start(), bad=check_far(F, rows, N))))
    elif a[0] == "--show":
        rows = exact_rows(tk(7 * (QI + 3)) + 10)
        F = build_family(rows, verbose=True)
        for p in F.pieces[int(a[1])]:
            print(p.name, "base", p.base, "P", p.P, "cnt", p.cnt)
            for i, S in enumerate(p.cls[:3]):
                print("   class", i, [(s[0], len(s[1]), s[2] if s[0] == 'R' else "") for s in S.segs])
