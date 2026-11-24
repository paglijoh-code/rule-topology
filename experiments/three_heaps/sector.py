"""three_heaps/sector.py — where is a table irregular?  Rare-block map: corner x (a<=b<=c chamber) is 'rare' if its 4^3 block
occurs <= R times among chamber corners.  Prints coarse maps of rare density on slices c = const over (a, b) bins."""
import sys, json, numpy as np
from lib3 import chain
from big import codes
def rare_map(S1, S2, N=300, R=2):
    T = chain(N, [S1, S2]); C = codes(T); M = C.shape[0]
    a, b, c = np.meshgrid(np.arange(M), np.arange(M), np.arange(M), indexing="ij")
    ch = (a <= b) & (b <= c)
    vals, inv, cnt = np.unique(C[ch], return_inverse=True, return_counts=True)
    rare = np.zeros(C.shape, bool); rare[ch] = cnt[inv] <= R
    return rare, ch
if __name__ == "__main__":
    S1 = tuple(json.loads(sys.argv[1])); S2 = tuple(json.loads(sys.argv[2])); N = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    rare, ch = rare_map(S1, S2, N); M = rare.shape[0]; bs = 10
    print(S1, "->", S2, "N", N, "rare fraction in chamber", round(rare[ch].mean(), 4))
    for c in (M // 2, 3 * M // 4, M - 1):
        print(f"slice c={c}: rows a (bin {bs}), cols b (bin {bs}); digit = rare density*9, '.' = 0, ' ' outside chamber")
        for a0 in range(0, c + 1, bs):
            row = ""
            for b0 in range(0, c + 1, bs):
                m = ch[a0:a0 + bs, b0:b0 + bs, c]
                if not m.any(): row += " "; continue
                f = rare[a0:a0 + bs, b0:b0 + bs, c][m].mean(); row += "." if f == 0 else str(min(9, int(f * 9.999)))
            print(f"{a0:4d} {row}")
