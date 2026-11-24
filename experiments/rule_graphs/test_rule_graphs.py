#!/usr/bin/env python3
"""test_rule_graphs.py : checks for graphs.py and exponent.py. Run: nice -n 10 python3 rule_graphs/test_rule_graphs.py"""
import os, sys
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
import numpy as np
import graphs, exponent

ok = True


def check(name, cond, extra=""):
    global ok
    print(("ok   " if cond else "FAIL ") + name + (" " + extra if extra else ""))
    ok &= bool(cond)


# --- 1. agreement with rulegraph.solve on small N, every graph type, both backends
cases = {
    "chain": (*graphs.chain((1, 2, 5, 6), (1, 2, 3, 4), (1, 3, 4))[:2], None),
    "chain6": ({"A": (1, 2), "B": (3, 4, 7), "C": (2, 5)}, {"A": ["B"], "B": ["C"]}, None),
    "cycle k=2": (*graphs.cycle((1, 2, 5, 6), (1, 2, 3, 4)), 2),
    "cycle k=3": (*graphs.cycle((2, 3, 6), (1, 4)), 3),
    "branch": (*graphs.branch((1, 2, 5, 6), (1, 2, 3, 4), (3, 5))[:2], None),
    "edge": ({"A": (1, 2, 5, 6), "B": (1, 2, 3, 4)}, {"A": ["B"]}, None),
}
for name, (S, G, bud) in cases.items():
    ref = graphs.rulegraph_reference(S, G, 16, bud)
    for use_c in ([True, False] if graphs.have_c() else [False]):
        got = graphs.solve_graph(S, G, 16, bud, use_c=use_c)
        check(f"{name} == rulegraph.solve (N=16, {'C' if use_c else 'python'})",
              set(got) == set(ref) and all((got[k] == ref[k]).all() for k in ref))

# --- 2. wall A with the python fallback (C absent): A->B, S1={1,2,5,6}, S2={1,2,3,4}
os.environ["M7B_NO_C"] = "1"
check("C backend disabled by M7B_NO_C", not graphs.have_c())
N = 3200
S, G = {"A": (1, 2, 5, 6), "B": (1, 2, 3, 4)}, {"A": ["B"]}
T = graphs.solve_graph(S, G, N)[("A", None)]
res, M = exponent.analyse(T)
Tr, Lr = exponent.rounds(M)
bad = []
for k in range(1, 7):
    want_row, want_col = 7 * k * k + 35 * k + 10, 35 + 10 * k
    j = list(Lr).index(want_col) if want_col in Lr else None
    if j is None or abs(int(Tr[j]) - want_row) > 3:
        bad.append((k, want_row, want_col, None if j is None else int(Tr[j])))
check("wall A rows 7k^2+35k+10 (+-3; +13 in the paper) settle at column 35+10k, k=1..6", not bad, str(bad))
check("wall A exponent fit ~ 0.5", 0.4 <= res["alpha"] <= 0.6, f"alpha={res['alpha']} range [{res['lo']},{res['hi']}]")
check("wall A bounce counter: round times quadratic (gamma=2 -> alpha_b 0.5)",
      res.get("alpha_bounce") and all(abs(x - 0.5) < 0.05 for x in res["alpha_bounce"]), str(res.get("alpha_bounce")))
os.environ.pop("M7B_NO_C")
if graphs.have_c():
    Tc = graphs.solve_graph(S, G, N)[("A", None)]
    check("C and python backends give the same wall-A table (N=3200)", (Tc == T).all())

# --- 3. plain periodic subtraction game: no boundary
for Sp in ((1, 3, 4), (2, 5, 7)):
    Tp = graphs.solve_graph({"A": Sp}, {}, 1200)[("A", None)]
    r, _ = exponent.analyse(Tp)
    check(f"periodic Sub{Sp}: no boundary (kind none or straight)",
          r["kind"] == "none" or r["alpha"] >= 0.9, f"kind={r['kind']} alpha={r['alpha']}")

# --- 4. can the estimator see alpha = 1/3 and 1/4?  (synthetic boundaries, wall-A-like: bounce k at
# row T_k = 52 + 40 k + c k^(1/alpha) + noise, each bounce lifts M by ~h in 1-3 record steps)
def synth(alpha, n, seed, h=10, t1=40, jit=3, K=23):
    rng = np.random.default_rng(seed)
    g = 1 / alpha
    c = (n - 30 - 52 - t1 * K) / K ** g          # bounce K lands near the last row
    M = np.zeros(n, int)
    lvl, k = 35, 1
    while True:
        t = int(52 + t1 * k + c * k ** g + rng.integers(-jit, jit + 1))
        if t >= n - 12:
            break
        st = int(rng.integers(1, 4))
        for s in range(st):
            lvl += max(1, int(round(h / st)) + int(rng.integers(-1, 2)))
            M[t + s * int(rng.integers(1, 5)):] = lvl
        k += 1
    return np.maximum.accumulate(M)


want = {0.5: (0.44, 0.58), 1 / 3: (0.27, 0.42), 0.25: (0.22, 0.36)}
for N_, n_rows in ((4000, 2000), (8000, 4000)):
    for tag, kw in (("mild noise", {}), ("heavy noise", dict(jit=10, h=6))):
        got = {}
        for al in want:
            got[al] = []
            for sd in range(6):
                r = exponent.fit_exponent(synth(al, n_rows, sd, **kw))
                got[al].append(r.get("alpha_bfit"))
        okr = all(v is not None and want[al][0] <= v <= want[al][1] for al in want for v in got[al])
        check(f"synthetic alpha 1/2,1/3,1/4 bands by bounce_fit, N={N_} {tag}", okr,
              " ".join(f"{al:.2f}:{min(v):.2f}-{max(v):.2f}" for al, v in got.items()))
        check(f"1/3 separated from 1/2 by bounce_fit, N={N_} {tag}", min(got[0.5]) > max(got[1 / 3]),
              f"1/2 min {min(got[0.5])} > 1/3 max {max(got[1 / 3])}")
        # the headline alpha (median of fits + bounce) is noisier: report only
        med = {round(al, 2): round(float(np.median([exponent.fit_exponent(synth(al, n_rows, sd, **kw))['alpha']
                                                      for sd in range(6)])), 3) for al in want}
        print("     info: median headline alpha per true alpha", med)

# --- 5. slow growth must not be called bounded
a_ = np.arange(1, 4000)
for cc in (8, 3):                                  # log boundary with several records after n/4
    Ml = np.zeros(4000, int)
    Ml[1:] = np.floor(cc * np.log(a_)).astype(int)
    r = exponent.fit_exponent(Ml)
    check(f"log boundary {cc} ln a: growing, small exponent", r["kind"] == "growing" and r["alpha"] <= 0.2,
          f"kind={r['kind']} alpha={r['alpha']} bfit={r.get('alpha_bfit')}")
for cc in (1.2, 0.8):                              # 1..2 records after n/4: 'slow', never 'bounded'
    Ml = np.zeros(4000, int)
    Ml[1:] = np.floor(cc * np.log(a_)).astype(int)
    r = exponent.fit_exponent(Ml)
    check(f"log boundary {cc} ln a: not 'bounded' (kind={r['kind']})", r["kind"] == "slow")
Msat = np.minimum(np.arange(4000) // 3, 40)        # truly saturated at row 120
check("saturating boundary is 'bounded'", exponent.fit_exponent(Msat)["kind"] == "bounded")

print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
