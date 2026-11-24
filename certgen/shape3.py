"""Symbolic stacks (shapes), with a preperiod N of g.
Symbolic stacks: shapes x0 y1^n1 x1 ... yj^nj xj z^omega, symbolic step, normalisation moves, decode.

Counters are kept numerically here (one concrete instance); every move / step is structural, i.e. its
counter delta and guard depend only on the words (learn.py exploits this)."""
from .stack3 import run, TINIT


class Shape:
    __slots__ = ('b', 'ys', 'n', 'z', 'rt')

    def __init__(self, b, ys, n, z, rt):
        self.b = [list(x) for x in b]      # boundaries x0..xj  (len j+1)
        self.ys = [list(y) for y in ys]    # block words (len j)
        self.n = list(n)                   # counters
        self.z = list(z)
        self.rt = rt                       # row tag of the NEXT row to compute (a mod p)

    def copy(self):
        return Shape(self.b, self.ys, self.n, self.z, self.rt)

    def key(self, W=None):
        """structural identity (counters excluded); row tag only through its transducer class"""
        return (tuple(map(tuple, self.b)), tuple(map(tuple, self.ys)), tuple(self.z), W.rcls[self.rt] if W else self.rt)

    def finite_len(self):
        return sum(map(len, self.b)) + sum(n * len(y) for n, y in zip(self.n, self.ys))


def decode(sh, length):
    out = list(sh.b[0])
    for i, y in enumerate(sh.ys):
        out += y * sh.n[i]
        out += sh.b[i + 1]
    while len(out) < length:
        out += sh.z
    return out[:length]


class Fail(Exception):
    pass


def sstep(W, sh, U=8):
    """symbolic step: returns (new shape with updated counters, delta list, gamma list).  Row tag advances."""
    x0 = sh.b[0]
    if len(x0) < max(W.N, W.m) + 2:
        raise Fail('x0 too short')
    cur, st = run(W, x0[1:], TINIT, sh.rt)
    nb, nys, delta, gamma = [], [], [], []
    for i, y in enumerate(sh.ys):
        cnt = 0
        while True:
            o, st1 = run(W, y, st, sh.rt)
            if st1 == st:
                break
            cur += o
            st = st1
            cnt += 1
            if cnt > U: raise Fail('block does not settle')
        nb.append(cur)
        nys.append(o)
        st = st1
        delta.append(-cnt); gamma.append(cnt)
        cur, st = run(W, sh.b[i + 1], st, sh.rt)
    # tail: state sequence at z-block starts is eventually periodic; unroll the pre-period into xj,
    # the output tail is the concatenation of the outputs over one state cycle (c copies of z).
    seen = {st: 0}
    outs = []
    while True:
        o, st1 = run(W, sh.z, st, sh.rt)
        outs.append(o)
        k = st1
        st = st1
        if k in seen: break
        seen[k] = len(outs)
        if len(outs) > max(U + 4, 4 * W.T // W.p + 8): raise Fail('tail does not settle')
    j = seen[k]
    for o in outs[:j]: cur += o
    o = [x for b in outs[j:] for x in b]
    tail_cnt = j
    nb.append(cur)
    new = Shape(nb, nys, [a + b for a, b in zip(sh.n, delta)], canon_z(W, o), W.ntag[sh.rt])
    return new, delta, gamma


# ---------------------------------------------------------------- normalisation

def extR(B, y):
    L = len(y); k = 0
    while k < len(B) and B[k] == y[k % L]: k += 1
    return k


def extL(B, y):
    L = len(y); k = 0
    while k < len(B) and B[-1 - k] == y[(L - 1 - k) % L]: k += 1
    return k


def minrot(y):
    L = len(y)
    best = min(range(L), key=lambda r: y[r:] + y[:r])
    return best


class Norm:
    def __init__(self, M, L, cf=2):
        self.M, self.L, self.cf = M, L, cf


def normalise(W, sh, P):
    """in-place; returns the list of moves.  Moves (all decode-preserving):
      ('rot',i,r)   y_i -> y_i[r:]+y_i[:r]; b_i += y[:r]; b_{i+1} = y[r:]+b_{i+1}; n_i -= 1   (guard n_i>=1)
      ('pull',i,'L'|'R')  one copy of y_i moves to end of b_i / start of b_{i+1}; n_i -= 1       (guard n_i>=1)
      ('abs',i,'L'|'R')   inverse: b_i ends with y_i / b_{i+1} starts with y_i -> n_i += 1
      ('trot',r) z -> z[r:]+z[:r], b_j += z[:r];  ('tpull',) b_j += z;  ('tabs',) b_j ends with z: drop it
      ('fold',b,s,c,y)  boundary b = u + y^c + v  ->  b_b = u, new block (y, c), b_{b+1} = v  (numeric c)
      ('drop',i)  block with n_i == 0 removed, boundaries merged"""
    M = P.M
    moves = []
    for _ in range(200):
        changed = False
        # drop empty blocks
        i = 0
        while i < len(sh.ys):
            if sh.n[i] == 0:
                moves.append(('drop', i))
                sh.b[i:i + 2] = [sh.b[i] + sh.b[i + 1]]
                del sh.ys[i]; del sh.n[i]
                changed = True
            else:
                i += 1
        # rotations to canonical
        for i, y in enumerate(sh.ys):
            r = minrot(y)
            if r:
                moves.append(('rot', i, r))
                sh.b[i] += y[:r]
                sh.b[i + 1] = y[r:] + sh.b[i + 1]
                sh.ys[i] = y[r:] + y[:r]
                sh.n[i] -= 1
                changed = True
        r = minrot(sh.z)
        if r:
            moves.append(('trot', r))
            sh.b[-1] += sh.z[:r]
            sh.z = sh.z[r:] + sh.z[:r]
            changed = True
        if changed:
            continue
        # margins
        for i, y in enumerate(sh.ys):
            L = len(y)
            while extR(sh.b[i + 1], y) >= M + L:
                sh.b[i + 1] = sh.b[i + 1][L:]; sh.n[i] += 1; moves.append(('abs', i, 'R')); changed = True
            while extR(sh.b[i + 1], y) < M and sh.n[i] >= 1:
                sh.b[i + 1] = y + sh.b[i + 1]; sh.n[i] -= 1; moves.append(('pull', i, 'R')); changed = True
            while extL(sh.b[i], y) >= M + L:
                sh.b[i] = sh.b[i][:-L]; sh.n[i] += 1; moves.append(('abs', i, 'L')); changed = True
            while extL(sh.b[i], y) < M and sh.n[i] >= 1:
                sh.b[i] = sh.b[i] + y; sh.n[i] -= 1; moves.append(('pull', i, 'L')); changed = True
        z = sh.z; L = len(z)
        while extL(sh.b[-1], z) >= M + L:
            sh.b[-1] = sh.b[-1][:-L]; moves.append(('tabs',)); changed = True
        while extL(sh.b[-1], z) < M:
            sh.b[-1] = sh.b[-1] + z; moves.append(('tpull',)); changed = True
        if changed:
            continue
        # fold
        if P.L and fold(W, sh, P, moves):
            continue
        break
    else:
        raise Fail('normalise does not terminate')
    return moves


def fold(W, sh, P, moves):
    L, M, cf = P.L, P.M, P.cf
    assert L % W.p == 0, 'block length must be a multiple of p'
    for bi, B in enumerate(sh.b):
        lo = 0
        if bi >= 1:
            lo = extR(B, sh.ys[bi - 1])
        hi = len(B)
        if bi < len(sh.ys):
            hi -= extL(B, sh.ys[bi])
        else:
            hi -= extL(B, sh.z)
        if hi - lo < L + 2 * M + cf * L: continue
        x = lo
        while x < hi - L:
            if B[x] == B[x + L]:
                a = x
                while x < hi - L and B[x] == B[x + L]: x += 1
                e = x + L                       # pattern covers [a, e)
                s0 = a + M
                if e - M - s0 >= L * cf:
                    y0 = B[s0:s0 + L]
                    r = minrot(y0)
                    s = s0 + r
                    y = B[s:s + L]
                    c = (e - M - s) // L
                    if c >= cf:
                        moves.append(('fold', bi, s, c, list(y)))
                        left, right = B[:s], B[s + c * L:]
                        sh.b[bi:bi + 1] = [left, right]
                        sh.ys.insert(bi, list(y)); sh.n.insert(bi, c)
                        return True
            else:
                x += 1
    return False


def canon_z(W, z):
    """reduce z to its minimal period that is a multiple of p (rotation kept)"""
    from math import gcd
    n = len(z)
    r = next(r for r in range(1, n + 1) if n % r == 0 and all(z[i] == z[i % r] for i in range(n)))
    return z[:r * W.p // gcd(r, W.p)]
