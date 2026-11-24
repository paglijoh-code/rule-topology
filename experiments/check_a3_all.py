"""Check every certificate against the brute-force solver (lead_a2.solve2) on all a, b <= N."""
import sys
from lead_a2 import solve2
from lead_a3 import Pair, predict, SUBSETS
N = int(sys.argv[1]) if len(sys.argv) > 1 else 600
bad = 0; n = 0
for S1 in SUBSETS:
    for S2 in SUBSETS:
        if S1 == S2: continue
        P = Pair(S1, S2); c = P.certify(); B = solve2(set(S1), set(S2), N)
        m = sum(1 for a in range(N + 1) for b in range(N + 1) if B[a][b] != predict(P, c, a, b))
        bad += m > 0; n += 1
        if m: print("MISMATCH", S1, S2, m)
print(f"{n} pairs, {bad} with mismatches, all a,b <= {N}")
