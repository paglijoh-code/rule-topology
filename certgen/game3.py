"""Brute force for G(S1, g) with preperiod: C row generator + independent full table (SPEC Game)."""
import os, subprocess, tempfile
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


class NotPeriodic(Exception):
    pass


def _build():
    exe = os.path.join(HERE, 'rowgen3')
    src = os.path.join(HERE, 'rowgen3.c')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        tmp = exe + '.%d' % os.getpid()
        subprocess.check_call(['cc', '-O2', '-o', tmp, src])
        os.replace(tmp, exe)
    return exe


def rows(S1, gpre, gper, N, D, T):
    """numpy uint8 array (N, D): R_a[d] = P(a, a+d); cells >= D are the T-periodic extension of the end."""
    exe = _build()
    fd, out = tempfile.mkstemp(dir=os.path.join(HERE, 'out') if os.path.isdir(os.path.join(HERE, 'out')) else None)
    os.close(fd)
    try:
        r = subprocess.run([exe, str(N), str(D), ','.join(map(str, S1)), ','.join(map(str, gpre)) or '-',
                            ','.join(map(str, gper)), str(T), out], capture_output=True)
        if r.returncode == 3:
            raise NotPeriodic(r.stderr.decode().strip())
        if r.returncode != 0:
            raise RuntimeError('rowgen3 exit %d %s' % (r.returncode, r.stderr.decode()))
        return np.fromfile(out, dtype=np.uint8).reshape(N, D)
    finally:
        os.unlink(out)


def gv(gpre, gper, x):
    return gpre[x] if x < len(gpre) else gper[(x - len(gpre)) % len(gper)]


def full_table(S1, gpre, gper, M):
    """Independent reference straight from SPEC: P[a][b] for a,b <= M (all pairs, both orders)."""
    P = [[False] * (M + 1) for _ in range(M + 1)]
    g = [gv(gpre, gper, x) for x in range(M + 1)]
    for t in range(2 * M + 1):               # by a+b
        for a in range(max(0, t - M), min(M, t) + 1):
            b = t - a
            if g[a] == g[b]:
                continue
            ok = True
            for s in S1:
                if s <= a and P[a - s][b]: ok = False; break
                if s <= b and P[a][b - s]: ok = False; break
            P[a][b] = ok
    return P


def crosscheck(S1, gpre, gper, T, M=400, D=700):
    """mismatches between rowgen3 and the full table, for all a, d with a + d <= M"""
    P = full_table(S1, gpre, gper, M)
    R = rows(S1, gpre, gper, M + 1, D, T)
    bad = 0
    for a in range(M + 1):
        for d in range(M + 1 - a):
            if bool(R[a, d]) != P[a][a + d]: bad += 1
    return bad


class Tab:
    """a selection of rows of the table (ring mode), indexable as R[a, cols] like the full array"""

    def __init__(self, idx, arr, N, D):
        self.pos = {int(a): i for i, a in enumerate(idx)}
        self.arr, self.shape, self.rows = arr, (N, D), [int(a) for a in idx]

    def __getitem__(self, key):
        a, sl = key
        return self.arr[self.pos[a], sl]


def rows_ring(S1, gpre, gper, N, D, T, pi, frm, w0, step):
    """(Tab of selected rows, pre array int32 per row a < N), see rowgen3.c ring mode"""
    exe = _build()
    outd = os.path.join(HERE, 'out')
    os.makedirs(outd, exist_ok=True)
    fs = []
    for _ in range(3):
        fd, f = tempfile.mkstemp(dir=outd); os.close(fd); fs.append(f)
    try:
        r = subprocess.run([exe, str(N), str(D), ','.join(map(str, S1)), ','.join(map(str, gpre)) or '-',
                            ','.join(map(str, gper)), str(T), fs[0], str(pi), fs[1], str(frm), str(w0), str(step),
                            fs[2]], capture_output=True)
        if r.returncode == 3:
            raise NotPeriodic(r.stderr.decode().strip())
        if r.returncode != 0:
            raise RuntimeError('rowgen3 exit %d %s' % (r.returncode, r.stderr.decode()))
        idx = np.fromfile(fs[2], dtype=np.int32)
        arr = np.fromfile(fs[0], dtype=np.uint8).reshape(len(idx), D)
        pre = np.fromfile(fs[1], dtype=np.int32)
        return Tab(idx, arr, N, D), pre
    finally:
        for f in fs: os.unlink(f)
