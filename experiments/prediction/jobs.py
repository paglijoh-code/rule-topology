#!/usr/bin/env python3
"""Prediction-test range (fixed before any scan): g = x mod n (pre 0, per n, pattern 0..n-1),
n in 5..11 with S1 subset of {1..12} containing 11 or 12 (S1 subset of {1..10} was scanned by census_10 R10/census_8),
n in {12, 13} with every nonempty S1 subset of {1..12}. Writes prediction/out/jobs.jsonl."""
import json, itertools, os
HERE = os.path.dirname(os.path.abspath(__file__))
out = open(os.path.join(HERE, 'out', 'jobs.jsonl'), 'w'); c = 0
for n in range(5, 14):
    for r in range(1, 13):
        for S in itertools.combinations(range(1, 13), r):
            if n <= 11 and not (11 in S or 12 in S): continue
            id_ = 's%s_n%d' % ('-'.join(map(str, S)), n)
            out.write(json.dumps(dict(id=id_, S1=list(S), gpre=0, gper=n, gpat=list(range(n)))) + '\n'); c += 1
print(c, 'pairs')
