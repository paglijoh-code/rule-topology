#!/usr/bin/env python3
"""Score the pre-registered predictions (PREREG.md) against the scan census. Written before the scan.
A sqrt wall := fit3 kind 'sqrt', exact, on a run with status ok to a = 100,000.
R1: Delta == T_R and s == T_R*P_R/per(g) (scored separately; no prediction = miss).
R0: Delta % T_R == 0 and, in every class, gap0 % P_R == 0 and s % P_R == 0.
B0 (baseline): Delta == 2*per(g)."""
import json, os, sys
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); O = os.path.join(HERE, 'out')
import hashlib
H = 'c2862edb9e510bc2e1779f8bcba12e0f3eb7132b9c3217ff8e704ccd6452111d'
assert hashlib.sha256(open(os.path.join(O, 'pred_all.jsonl'), 'rb').read()).hexdigest() == H, 'prediction file changed since PREREG'
jobs = [json.loads(l) for l in open(os.path.join(O, 'jobs.jsonl'))]
name = lambda j: 's' + '-'.join(map(str, j['S1'])) + '_g' + ''.join(map(str, j['gpat'])) + '_p0'
pred = {json.loads(l)['id']: json.loads(l) for l in open(os.path.join(O, 'pred_all.jsonl'))}
byname = {name(j): (j, pred.get(j['id'], {})) for j in jobs}
rows = []; cnt = dict(routed=0, sqrt=0, linear=0, nofit=0, notok=0)
for l in open(os.path.join(O, 'census.jsonl')):
    c = json.loads(l); cnt['routed'] += 1; f = c['fit']
    if c['status'] != 'ok' or c['a_stop'] < 100000: cnt['notok'] += 1; continue
    k = f.get('kind', 'nofit')
    if k == 'sqrt' and f.get('exact'):
        cnt['sqrt'] += 1
        j, p = byname[c['name']]; D, s = f['Delta'], f['s']
        T, P = p.get('T_R'), p.get('P_R')
        r = dict(name=c['name'], n=j['gper'], S1=j['S1'], q=f['q'], Delta=D, s=s, lam=str(Fraction(s, D)), T_R=T, P_R=P,
                 Delta_pred=p.get('Delta_pred'), s_pred=p.get('s_pred'),
                 R1_Delta=p.get('Delta_pred') == D, R1_s=p.get('s_pred') == str(s),
                 R1_lam=p.get('lam_pred') == str(Fraction(s, D)),
                 R0=bool(T and P and D % T == 0 and s % P == 0 and all(cl['gap0'] % P == 0 for cl in f['classes'])),
                 B0=D == 2 * j['gper'])
        rows.append(r)
    elif k == 'linear': cnt['linear'] += 1
    else: cnt['nofit'] += 1
tot = len(rows)
summary = dict(counts=cnt, walls=tot, **{h: sum(r[h] for r in rows) for h in ('R1_Delta', 'R1_s', 'R1_lam', 'R0', 'B0')})
json.dump(dict(summary=summary, walls=rows), open(os.path.join(O, 'score.json'), 'w'), indent=1)
for r in rows:
    print(r['name'][:46].ljust(46), 'q', r['q'], 'Δ', r['Delta'], 's', r['s'], '| T_R', r['T_R'], 'P_R', r['P_R'],
          '| R1Δ', 'hit' if r['R1_Delta'] else 'MISS', 'R1s', 'hit' if r['R1_s'] else 'MISS', 'R0', 'hit' if r['R0'] else 'MISS', 'B0', 'hit' if r['B0'] else 'miss')
print(json.dumps(summary))
