"""Recheck of the cross-class curved candidate push:sub:1,3,6>wsub:5,6,7 at N=8000.

    nice -n 10 python3 game_classes/recheck_candidate.py    (about 15 s, under 100 MB)

Uses game_classes/census.table for the start-mode table and rule_graphs/exponent for the wall and round detection,
then checks the exact law t_k = 6k^2 + 126k + 779, w_k = 136 + 12k on every detected round with t_k >= 779.
"""
import sys, importlib.util
import numpy as np
sys.path.insert(0, 'game_classes')
sp = importlib.util.spec_from_file_location('c7a', 'game_classes/census.py')
c7a = importlib.util.module_from_spec(sp); sp.loader.exec_module(c7a)
sys.path.insert(0, 'rule_graphs')
import exponent

N = 8000
T = np.asarray(c7a.table('push:sub:1,3,6>wsub:5,6,7', N)).astype(np.int8)
res, M = exponent.analyse(T)
Tr, Lr = exponent.rounds(M)
print('kind', res['kind'], 'alpha', res['alpha'], 'range', (res['lo'], res['hi']), 'bounce fit', res.get('alpha_bfit'))
law = [(int(t), int(w)) for t, w in zip(Tr, Lr) if t >= 779]
bad = [(k, t, w) for k, (t, w) in enumerate(law) if (t, w) != (6 * k * k + 126 * k + 779, 136 + 12 * k)]
print('rounds checked', len(law), 'last', law[-1], 'mismatches', bad)
sys.exit(1 if bad or len(law) < 10 else 0)
