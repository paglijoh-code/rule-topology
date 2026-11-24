"""Two-medium + tail model:  row(a)[d] = alpha[u] (d<p1) | beta[u] (p1<=d<p2) | tau[v] (d>=p2),
u = (d - w_k - 5 r) mod 35,  v = (d - w_k - 5 r) mod 10,  a = t_k + r,  w_k = 35 + 10 k.
Fits alpha, beta, tau from k=K rows, then reports for every row whether the 3-seam form holds."""
import sys
sys.path.insert(0,__import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from common import *
def fit(R,K=50,rows=range(60,400)):
    wK=w(K); al={};be={};ta={}
    for r in rows:
        a=t(K)+r; row=R[a]
        pr=pre(R,a)
        # left-run: from the left until first break of 35-periodicity extension: use 35-periodic run starting 0
        x=0
        while x+35<pr and row[x]==row[x+35]: x+=1
        for d in range(0,x):   # inside left run (periodic with period 35 from 0 to x+34)
            u=(d-wK-5*r)%35
            if al.setdefault(u,row[d])!=row[d]: raise Exception("alpha conflict")
        for d in range(pr,pr+60):
            v=(r%7,(d-wK)%10)
            if ta.setdefault(v,row[d])!=row[d]: raise Exception("tail conflict")
    return al,ta

def fit_beta(R,al,K=50,rows=range(60,400)):
    wK=w(K); be={}
    for r in rows:
        a=t(K)+r; row=R[a]; pr=pre(R,a)
        x=0
        while (row[x]==al[(x-wK-5*r)%35]): x+=1
        for d in range(x,min(x+60,pr-20)):
            u=(d-wK-5*r)%35
            if be.setdefault(u,row[d])!=row[d]: raise Exception("beta conflict r=%d"%r)
    return be

def seams(row,a,r,k,al,be,ta,pr):
    """greedy 3-seam parse; returns (p1,p2) or None. p1 = first deviation from alpha, p2 = first deviation from beta after p1."""
    wk=w(k)
    p1=0
    while p1<len(row)-20 and row[p1]==al[(p1-wk-5*r)%35]: p1+=1
    p2=p1
    while p2<len(row)-20 and row[p2]==be[(p2-wk-5*r)%35]: p2+=1
    return p1,p2

def fit_R(R,K=50,margin=20):
    """gamma, delta in the u = d - w_K - 5r frame, from R-phase rows of round K."""
    wK=w(K); g=14*(K+3); ga={}; de={}
    for r in range(12*K+45, g-20):
        a=t(K)+r; row=R[a]; pr=pre(R,a)
        x=0
        while x+35<pr and row[x]==row[x+35]: x+=1
        for d in range(0,x):
            u=(d-wK-5*r)%35
            if ga.setdefault(u,row[d])!=row[d]: raise Exception("gamma")
        for d in range(x+35+margin,pr-20):
            u=(d-wK-5*r)%35
            if de.setdefault(u,row[d])!=row[d]: raise Exception("delta")
    return ga,de
