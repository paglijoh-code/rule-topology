"""three_heaps/ana_cx.py N — chamber block complexity cx(n) and local log-log exponents, from big/N/*.cx."""
import sys, glob, math, os
N = int(sys.argv[1]); grid = [g for g in (300, 450, 600, 800, 1000, 1200, 1500, 2000, 2500, 3000, 3500, 4000) if g <= N + 1]
for f in sorted(glob.glob(f"big/{N}/*.cx")):
    cx = dict(tuple(map(int, l.split())) for l in open(f))
    v = [cx[min(g, N + 1)] for g in grid]
    ex = [round(math.log(v[i + 1] / v[i]) / math.log(grid[i + 1] / grid[i]), 2) if v[i + 1] > v[i] else 0 for i in range(len(v) - 1)]
    print(f"{os.path.basename(f)[:-3]:22s}", " ".join(map(str, v)), "| exp", ex)
