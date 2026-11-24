"""Extra checks of two rule_graph_laws laws (run: python3 rule_graph_laws/laws_check.py).
L-SYM: symmetric graph (every edge reversed) with budget k has X_2 = X_0.
L-RET: chain X -> A -> B -> A has the P-set of X -> A (end return), and
       mid-chain return: X -> A -> B -> A -> Y vs X -> A -> Y."""
import random, sys
sys.path.insert(0, 'rule_graph_laws')
import rgenum as E
N = 40
blocks = E.make_named(N) + E.make_random(N, n_each=60, seed=7)
rng = random.Random(11)
sym_bad = 0
for t in range(400):
    n = rng.randint(2, 5)
    bs = [rng.choice(blocks) for _ in range(n)]
    edges = set()
    for _ in range(rng.randint(1, 6)):
        u, v = rng.randrange(n), rng.randrange(n)
        edges |= {(u, v), (v, u)}
    adj = {}
    for u, v in edges:
        adj.setdefault(u, []).append(v)
    s = E.budget_seq(bs, adj, 6)
    if any(s[j] != s[j % 2] for j in range(7)):
        sym_bad += 1
print("L-SYM violations:", sym_bad, "of 400 random symmetric graphs, 2-5 nodes, k<=6")
end_bad = mid_bad = mid_n = 0
for t in range(1500):
    x, a, b, y = (rng.choice(blocks) for _ in range(4))
    c1 = E.eval_acyclic([x, a, b, a], {0: [1], 1: [2], 2: [3]})[0]
    c2 = E.eval_acyclic([x, a], {0: [1]})[0]
    end_bad += c1 != c2
    m1 = E.eval_acyclic([x, a, b, a, y], {0: [1], 1: [2], 2: [3], 3: [4]})[0]
    m2 = E.eval_acyclic([x, a, y], {0: [1], 1: [2]})[0]
    mid_bad += m1 != m2
print("L-RET end violations:", end_bad, "of 1500; mid-chain violations:", mid_bad, "of 1500")
