#!/usr/bin/env python3
"""switching.py : switching variants the 2-cycle parity lemma does not cover.

loop3 : one-way loop A->B->C->A, push budget k = 1..9 (a push cannot be undone in one step).
        For each wall (A,B) and a sample of C, start-mode tables T_k at N; records the kind per k
        and which earlier budget T_k equals exactly (period in k).
cost  : A <-> B, a switch also removes exactly c in {1,2,3} from one pile; unlimited switches
        (finite because each switch shrinks a pile). Start-mode table analysed.
Run: nice -n 10 python3 rule_graphs/switching.py loop3 2000 rule_graphs/loop3_2000.jsonl
     nice -n 10 python3 rule_graphs/switching.py cost 4000 rule_graphs/cost4000.jsonl
"""
import os, sys, json, gc, ctypes, subprocess, random
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs, exponent


def _lib2():
    so, src = os.path.join(H, '_sub2.so'), os.path.join(H, 'sub2.c')
    if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
        subprocess.run(['cc', '-O2', '-shared', '-fPIC', '-o', so, src], check=True)
    L = ctypes.CDLL(so)
    L.solve_pair.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p,
                             ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p]
    return L


def cost_pair(A, B, c, N):
    L = _lib2(); n1 = N + 1
    oA = np.empty((n1, n1), np.int8); oB = np.empty((n1, n1), np.int8)
    a = np.array(sorted(A), np.int32); b = np.array(sorted(B), np.int32)
    L.solve_pair(n1, len(a), a.ctypes.data, len(b), b.ctypes.data, c, oA.ctypes.data, oB.ctypes.data)
    return oA, oB


def cost_pair_ref(A, B, c, N):
    """direct recursion, for the self-test"""
    from functools import lru_cache
    @lru_cache(None)
    def P(m, x, y):
        S = A if m == 0 else B
        opts = [(m, x - s, y) for s in S if s <= x] + [(m, x, y - s) for s in S if s <= y]
        opts += [(1 - m, x - c, y)] * (c <= x) + [(1 - m, x, y - c)] * (c <= y)
        return all(not P(*o) for o in opts)
    return [np.array([[int(P(m, x, y)) for y in range(N + 1)] for x in range(N + 1)]) for m in (0, 1)]


def walls():
    W = [json.loads(l) for l in open(os.path.join(H, '..', 'census_10', 'walls_exact.jsonl'))]
    return [w for w in W if w['S2_example']]


def an(T, N):
    r, _ = exponent.analyse(T, pmax=400, tail=min(1200, N // 4))
    return r['kind'], r['alpha'], r.get('n_rounds')


if __name__ == '__main__':
    mode, N, OUT = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    if mode == 'test':
        for A, B, c in (((1, 2, 5, 6), (1, 2, 3, 4), 1), ((2, 3), (1, 4), 2), ((1, 3, 4), (2, 5), 3)):
            got, ref = cost_pair(A, B, c, 14), cost_pair_ref(A, B, c, 14)
            print('cost', A, B, c, 'ok' if all((g == r).all() for g, r in zip(got, ref)) else 'FAIL')
        sys.exit()
    rng = random.Random(3)
    with open(OUT, 'w') as f:
        for w in walls():
            A, B, tag = tuple(w['S1']), tuple(w['S2_example']), w['tag']
            if mode == 'loop3':
                Cs = [tuple(sorted(rng.sample(range(1, 8), rng.randint(1, 7)))) for _ in range(12)]
                for C in Cs:
                    K = 9
                    res = graphs.solve_graph({'A': A, 'B': B, 'C': C}, {'A': ['B'], 'B': ['C'], 'C': ['A']}, N, K)
                    T = [res[('A', k)] for k in range(K + 1)]
                    for k in range(1, K + 1):
                        kind, al, nr = an(T[k], N)
                        eq = [j for j in range(k) if (T[k] == T[j]).all()]
                        f.write(json.dumps(dict(wall=tag, C=C, k=k, kind=kind, alpha=al, n_rounds=nr, eq_earlier=eq)) + '\n')
                    del res, T; gc.collect()
            else:
                for c in (1, 2, 3):
                    for swap in (False, True):
                        X, Y = (B, A) if swap else (A, B)
                        TA, TB = cost_pair(X, Y, c, N)
                        kind, al, nr = an(TA, N)
                        f.write(json.dumps(dict(wall=tag, start='B' if swap else 'A', c=c, kind=kind, alpha=al, n_rounds=nr)) + '\n')
            f.flush(); print(tag, flush=True)
