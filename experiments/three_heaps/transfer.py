"""three_heaps/transfer.py — rule_graph_laws block-dependent laws on two heaps (face c = 0) vs three heaps, Sub(S) blocks S ⊆ {1..4}, N = 40.
commuting: R1->R2->R3 == R1->R3->R2 ; fork R1->{R2,R3} equals one of its branches R1->R2, R1->R3; return law; drop-out."""
import itertools, json
import numpy as np
from multiprocessing import Pool
from lib3 import phi
N = 40
subs = [s for r in range(1, 5) for s in itertools.combinations(range(1, 5), r)]
P = {}
def job(t):
    s1, s2, s3 = t
    P2, P3 = phi(N, s2), phi(N, s3)
    c23 = phi(N, s1, phi(N, s2, P3)); c32 = phi(N, s1, phi(N, s3, P2))
    fk = phi(N, s1, P2 | P3); b2 = phi(N, s1, P2); b3 = drop = phi(N, s1, P3)
    f = lambda A, B: (bool((A == B).all()), bool((A[:, :, 0] == B[:, :, 0]).all()))
    ret = phi(N, s1, phi(N, s2, phi(N, s1)))  # A->B->A == A ?

    return dict(t=t, comm=f(c23, c32), fork=(f(fk, b2)[0] or f(fk, b3)[0], f(fk, b2)[1] or f(fk, b3)[1]),
                ret=f(ret, phi(N, s1)), drop=f(c23, drop))
if __name__ == "__main__":
    with Pool(8) as p: R = p.map(job, list(itertools.product(subs, repeat=3)), chunksize=8)
    json.dump(R, open("raw/transfer_N40.json", "w"))
    for k in ("comm", "fork", "ret", "drop"):
        n3 = sum(r[k][0] for r in R); n2 = sum(r[k][1] for r in R)
        print("%-5s holds on 3 heaps %4d / %d ; on 2 heaps (face) %4d ; 2-heap-only %d" % (k, n3, len(R), n2, sum(r[k][1] and not r[k][0] for r in R)))
