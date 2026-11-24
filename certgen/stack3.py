"""Stacks Sigma_a (m-bit letters) and the row transducer of docs/certificate-format.md, with preperiod N (dtag, row tag)."""
import numpy as np
from math import gcd
from .game3 import gv


class Wall:
    def __init__(self, name, S1, gpre, gper, T):
        self.name, self.S1, self.gpre, self.gper, self.T = name, list(S1), list(gpre), list(gper), T
        self.m = max(S1)
        self.N, self.p = len(gpre), len(gper)
        N, p = self.N, self.p
        self.nt = N + p                    # number of tags
        self.mask = 0
        for s in S1:
            self.mask |= 1 << (s - 1)
        g = lambda x: gv(self.gpre, self.gper, x)
        # tst[rt][dtag] = g(A) != g(A + d)   (computed from the tags: gv rt != gv (rt + dtag))
        self.tst = [[g(rt) != g(rt + dt) for dt in range(self.nt)] for rt in range(self.nt)]
        self.ntag = [rt + 1 if rt + 1 < self.nt else N for rt in range(self.nt)]   # tag of the next row / next d
        cl = {}
        self.rcls = [cl.setdefault(tuple(t), len(cl)) for t in self.tst]

    def rtag(self, A):
        return A if A < self.N else self.N + (A - self.N) % self.p

    def dtag(self, d):
        return self.rtag(d)


TINIT = (0, 0, 0, 0)


def run(W, letters, st, rt):
    """Mirror of lean/FamilyStack.lean `tstep`.  st = (u0, hist, dtag, cnt), cnt = min(d, m).
    Returns (outputs, st')."""
    u0, hist, dtag, cnt = st
    m, mask, S1 = W.m, W.mask, W.S1
    tst = W.tst[rt]
    dn = W.ntag
    hm = (1 << m) - 1
    top = (1 << (m - 1)) - 1
    out = []
    for x in letters:
        u0n = x if cnt == 0 else u0
        if cnt >= m:
            nb = 1 if (tst[dtag] and not (x & mask) and not (hist & mask)) else 0
        else:
            nb = 1 if tst[dtag] else 0
            if nb:
                for s in S1:
                    if (x >> (s - 1)) & 1: nb = 0; break
                    if s <= cnt:
                        if (hist >> (s - 1)) & 1: nb = 0; break
                    elif (u0n >> (s - cnt - 1)) & 1: nb = 0; break
        out.append((nb + 2 * (x & top)) & hm)
        u0 = u0n if cnt + 1 < m else 0
        hist = ((hist << 1) | nb) & hm
        dtag = dn[dtag]
        cnt = cnt + 1 if cnt < m else m
    return out, (u0, hist, dtag, cnt)


def canon(W, pre, z):
    """canonical (pre, z): z minimal period that is a multiple of p, pre minimal."""
    pre, z = list(pre), list(z)
    n = len(z)
    r = next(r for r in range(1, n + 1) if n % r == 0 and all(z[i] == z[i % r] for i in range(n)))
    q = r * W.p // gcd(r, W.p)
    z = z[:q]
    while pre and pre[-1] == z[-1]:
        z = [pre.pop()] + z[:-1]
    return pre, z


def letters_of(W, R, a):
    """all letters of Sigma_a computable from the table R (rows 0..a)."""
    D = R.shape[1]
    m = W.m
    L = D - m
    let = np.zeros(L, dtype=np.int64)
    for i in range(m):
        if a - i >= 0:
            let |= R[a - i, i:i + L].astype(np.int64) << i
    return let.tolist()


def from_rows(W, R, a):
    """Brute-force Sigma_a from the row table R (rows 0..a): canonical (pre, z). Row a-i<0 reads 0."""
    let = letters_of(W, R, a)
    L = len(let)
    T = W.T
    W_ = 6 * T
    q = None
    for qq in range(W.p, 4 * T * W.p + 1, W.p):
        if all(let[x] == let[x + qq] for x in range(L - qq - W_, L - qq)):
            q = qq
            break
    assert q is not None
    e = L - q - W_
    while e > 0 and let[e - 1] == let[e - 1 + q]:
        e -= 1
    return canon(W, let[:e], let[e:e + q])


def decode(pre, z, n):
    out = list(pre)
    while len(out) < n:
        out += z
    return out[:n]
