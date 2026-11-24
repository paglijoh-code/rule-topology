"""Trip-cost law test: medium (Q, tau, sigma) and glider speeds for pairs A and B.
Usage: python speeds.py   (dumps rows via out/wallscan into out/speeds/, prints JSON)"""
import json, os, subprocess, sys
import numpy as np
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "speeds")
N, D, PMAX = 20000, 1500, 200
PAIRS = {
    "A": dict(S1="1,2,5,6", gpre=0, gper=5, pat="0,1,2,3,4", s=14, Delta=10,
              tk=lambda k: 7*k*k + 77*k + 178, wall=lambda k: 65 + 10*k, window=(10000, 15000)),
    "B": dict(S1="1,2,3,4,7,8", gpre=0, gper=6, pat="0,1,2,3,2,4", s=36, Delta=36,
              tk=lambda k: 18*k*k + 258*k + 859, wall=lambda k: 208 + 36*k, window=(2000, 4600)),
}

def dump(name, p):
    f = os.path.join(OUT, name + ".bin")
    js = os.path.join(OUT, name + ".json")
    if not os.path.exists(js):
        env = dict(os.environ, WS_DUMP=f)
        r = subprocess.run([os.path.join(HERE, "out", "wallscan"), str(N), str(D), str(PMAX), p["S1"],
                            str(p["gpre"]), str(p["gper"]), p["pat"]], env=env, capture_output=True, text=True)
        open(js, "w").write(r.stdout)
    info = json.loads(open(js).read().strip().splitlines()[-1])
    rows = np.fromfile(f, dtype=np.uint8).reshape(-1, D)  # only a_stop rows are written
    return rows, info

def wall_of_rows(info):
    w = np.zeros(len(info["rows"]) if "rows" in info else info["a_stop"] + 1, int)
    cur = 0; recs = info["records"]; j = 0
    for a in range(len(w)):
        while j < len(recs) and recs[j][0] <= a:
            cur = recs[j][1]; j += 1
        w[a] = cur
    return w

def medium(rows, wall, a0, a1):
    # bulk window: d in [60, wall-80], rows a0..a1 (rows sampled)
    res = {}
    a_s = np.linspace(a0, a1, 41).astype(int)[1:]
    # Q: smallest q with high agreement across d in window (use rows mostly outside glider -> take max over rows)
    Qs = {}
    for q in range(1, 120):
        fr = []
        for a in a_s[:40]:
            w = wall[a]; lo, hi = 60, w - 80
            if hi - lo < q + 20: continue
            r = rows[a]; fr.append(np.mean(r[lo:hi-q] == r[lo+q:hi]))
        Qs[q] = float(np.median(fr)) if fr else 0
    Q = next((q for q in Qs if Qs[q] > 0.97), None)
    best = None
    for tau in range(1, 40):
        for sigma in sorted(range(-60, 61), key=lambda x: (abs(x), -x)):
            fr = []
            for a in a_s[:40]:
                w = wall[a]; lo, hi = 80, w - 80
                lo2 = max(lo, lo + sigma); hi2 = min(hi, hi + sigma)
                if hi2 - lo2 < 20: continue
                fr.append(np.mean(rows[a][lo2:hi2] == rows[a - tau][lo2 - sigma:hi2 - sigma]))
            sc = float(np.median(fr)) if fr else 0
            if sc > 0.97:
                return Q, (tau, sigma, sc), Qs
    return Q, None, Qs

def fit(xs, ys):
    xs = np.array(xs, float); ys = np.array(ys, float)
    A = np.polyfit(xs, ys, 1)
    return A[0]

def track(rows, wall, tau, sigma, k_round, p):
    t0 = p["tk"](k_round); t1 = p["tk"](k_round + 1)
    # defect cells
    tr = []
    for a in range(t0 - 3, t1 + 3):
        w = wall[a]
        d = np.arange(max(sigma, 0) + 1, w - 2)
        defect = rows[a][d] != rows[a - tau][d - sigma]
        idx = d[defect]
        tr.append((a, int(idx.min()) if len(idx) else -1, int(idx.max()) if len(idx) else -1, len(idx), int(w)))
    return tr

# lattice used for tracking (B: auto search is fooled by row-dependent phase, (6,6) is the best single step)
FORCE = {"A": (1, 5), "B": (6, 6)}

def edges(rows, wall, tau, sigma, k, p, dmin=30, maxdef=None):
    """Per row defect set (lattice-shifted comparison); returns list of (a, min, max, n)."""
    t0, t1 = p["tk"](k), p["tk"](k + 1)
    out = []
    for a in range(t0, t1):
        d = np.arange(dmin, wall[a] - 2)
        idx = d[rows[a][d] != rows[a - tau][d - sigma]]
        if len(idx) and (maxdef is None or len(idx) < maxdef):
            out.append((a, int(idx.min()), int(idx.max()), len(idx)))
    return out

def slope(pts):
    x = np.array([q[0] for q in pts], float); y = np.array([q[1] for q in pts], float)
    m, c = np.polyfit(x, y, 1); return float(m), float(c)

def glider_fit(name, rows, wall, p, k):
    tau, sigma = FORCE[name]
    t0, t1 = p["tk"](k), p["tk"](k + 1)
    ed = edges(rows, wall, tau, sigma, k, p, maxdef=(None if name == "A" else 40))
    res = {"round_len": t1 - t0, "wall_start": int(wall[t0 + 10]), "wall_end": p["wall"](k)}
    if name == "A":
        lead = [q for q in ed if q[1] > 20 and q[0] < t0 + 460]
        m, c = slope(lead)
        res.update(left_slope_cells_per_row=m, left_rows_per_cell=1 / -m,
                   left_leading_edge_reaches_d0_row=-c / m, n_pts=len(lead))
        # return leg: invisible (stationary in lattice frame); inferred from the rest of the round
        res["rows_after_left_leg"] = t1 - int(-c / m)
    else:
        lead = [q for q in ed if 40 < q[1] < 260 and q[0] < t0 + 215]       # leading (leftmost) edge
        trail = [q for q in ed if q[0] > t0 + 100 and q[0] < t0 + 372 and q[2] < 300 and q[2] > 40]  # right edge of band
        m, c = slope(lead); m2, c2 = slope(trail)
        res.update(left_slope_cells_per_row=m, left_rows_per_cell=1 / -m,
                   trailing_edge_slope=m2, trailing_edge_reaches_d0_row=-c2 / m2,
                   trailing_edge_at_round_start=m2 * t0 + c2)
    return res

def main():
    summ = {}
    for name, p in PAIRS.items():
        rows, info = dump(name, p)
        wall = wall_of_rows(info)
        a_stop = info["a_stop"]
        lo, hi = p["window"]; hi = min(hi, a_stop - 5)
        Q, lat, Qs = medium(rows, wall, (lo + hi) // 2 - 100, (lo + hi) // 2 + 100) if False else medium(rows, wall, lo, hi)
        out = dict(status=info["status"], a_stop=a_stop, tail_periods=info["tail_periods"], Q=Q,
                   lattice=None if lat is None else dict(tau=lat[0], sigma=lat[1], match=lat[2]),
                   s=p["s"], Delta=p["Delta"], s_over_Delta=str(Fraction(p["s"], p["Delta"])))
        if lat is not None:
            tau, sigma = lat[0], lat[1]
            # pick a round fully in window
            k = 0
            while p["tk"](k + 1) < lo: k += 1
            if p["tk"](k + 1) + 5 > a_stop: k -= 1
            tr = track(rows, wall, tau, sigma, k, p)
            np.save(os.path.join(OUT, name + "_track.npy"), np.array(tr))
            out["round_k"] = k; out["round_start"] = p["tk"](k); out["round_len"] = p["tk"](k + 1) - p["tk"](k)
            out["wall"] = p["wall"](k)
            out["track_sample"] = [t for t in tr[::max(1, len(tr)//40)]]
        out["glider_fit"] = glider_fit(name, rows, wall, p, out.get("round_k", 0)) if lat is not None else None
        out.pop("track_sample", None)
        summ[name] = out
    print(json.dumps(summ))

if __name__ == "__main__":
    main()
