"""three_heaps/ana_prof.py N PAIR [step] — radial profile around the main diagonal from big/N/PAIR.prof.
Per slab s (bin 20): r*_rare = outer edge of the last radius bin (width 4, scanning out from 0) with rare-block density > 0.3
(same rule as tube2.py); r*_def = same for period-60 defect density > 0.05; only bins whose disc lies inside the cube."""
import sys, math, collections
N = int(sys.argv[1]); pair = sys.argv[2]; step = int(sys.argv[3]) if len(sys.argv) > 3 else 100
d = collections.defaultdict(dict)
for l in open(f"big/{N}/{pair}.prof"):
    s, r, t, ra, df = map(int, l.split()); d[s][r] = (t, ra, df)
def edge(dens, thr):
    rs = 0
    for i, x in enumerate(dens):
        if x > thr: rs = 4 * (i + 1)
        elif i * 4 > rs + 12: break
    return rs
out = []
for s in sorted(d):
    if s < 40 or s % step: continue
    rmax = int((N - 64 - (s + 20) / 3) / math.sqrt(2 / 3))   # discs of radius <= rmax lie in the cube (with room for the +60 defect shift)
    nb = min(100, rmax // 4)
    if nb < 3: continue
    rare = [d[s][r][1] / d[s][r][0] if r in d[s] and d[s][r][0] else 0 for r in range(0, 4 * nb, 4)]
    dfc = [d[s][r][2] / d[s][r][0] if r in d[s] and d[s][r][0] else 0 for r in range(0, 4 * nb, 4)]
    rr, rd = edge(rare, 0.3), edge(dfc, 0.05)
    tail = sum(d[s][r][1] for r in range(0, 4 * nb, 4) if r in d[s] and r >= rr + 20) / max(1, sum(d[s][r][0] for r in range(0, 4 * nb, 4) if r in d[s] and r >= rr + 20))
    out.append((s, rr, rd, round(tail, 4), 4 * nb))
    print(s, "r*_rare", rr, "r*_def", rd, "rare density beyond r*+20:", round(tail, 4), "(r<=", 4 * nb, ")")
