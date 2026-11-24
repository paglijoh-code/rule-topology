"""three_heaps/selftest.py — C solvers vs independent brute force."""
import numpy as np, random, itertools
from lib3 import chain, phi, brute_chain
random.seed(1)
subs = [tuple(s) for r in range(1, 5) for s in itertools.combinations(range(1, 5), r)]
ok = 0
for trial in range(40):
    k = random.choice([1, 2, 2, 3]); sets = [random.choice(subs) for _ in range(k)]
    N = 12 if k < 3 else 9
    A = chain(N, sets); B = brute_chain(N, sets)
    X = phi(N, sets[-1]);
    for s in reversed(sets[:-1]): X = phi(N, s, X)
    assert (A == B).all() and (X == B).all(), sets
    ok += 1
print("selftest PASS", ok, "chains (C chain3, C phi3 vs Python game brute force)")
from lib3 import cycle, cycle_py
c = 0
for trial in range(25):
    n = random.choice([1, 2, 3, 3, 4]); sets = [random.choice(subs) for _ in range(n)]
    a = cycle(8, sets); b = cycle_py(8, sets)
    assert a == b, (sets, a, b); c += 1
print("selftest PASS", c, "budgeted cycles (C cyc3 vs Python phi3 iteration)")
