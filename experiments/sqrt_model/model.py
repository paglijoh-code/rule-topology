#!/usr/bin/env python3
"""Explicit tile model of the table for S1={1,2,5,6}, g=01234 .

Words are learned once, from a single round (K=50) of the exact table, then every row of every round
k=KMIN..KMAX is generated from the words + seam formulas and compared with the exact table.
Usage: model.py [KMIN] [KMAX]     (needs scratch R.bin from rowgen: 24000 rows x 816 cols)"""
import sys, numpy as np
sys.path.insert(0,__import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from tilemodel import *
from collections import Counter

def learn(R,K=50):
    al,ta=fit(R,K); be=fit_beta(R,al,K); ga,de=fit_R(R,K)
    return al,be,ga,de,ta

def ws(m): return "".join(".#"[m[i]] for i in range(35))

def gen_row(k,r,W,n):
    """cells 0..n-1 of row t_k + r from the model (numpy); W = (al,be,ga,de,ta,G,Pw,Qw,E)."""
    al,be,ga,de,ta,G,Pw,Qw,E=W
    wk=w(k); gp=14*(k+3)
    d=np.arange(n); e=d-wk
    A=lambda M:np.array([M[i] for i in range(35)],dtype=np.uint8)[(d-wk-5*r)%35]
    T=np.array([ta[(r%7,i)] for i in range(10)],dtype=np.uint8)[e%10]
    if r<12*k+32:                       # L phase: alpha | beta | tail
        p1=wk-9+5*(r%6)-5*(r//6); p2=wk+Pw[r%7]
        return np.where(d<p1,A(al),np.where(d<p2,A(be),T))
    if r==gp-1:                         # last row before the jump: glider meets the wall (explicit word E)
        Ev=np.array(E,dtype=np.uint8)
        out=np.where(d<wk-10,A(ga),T)
        m=(e>=-10)&(e<40)
        out[m]=Ev[e[m]+10]
        return out
    s=gp-r                              # R phase: gamma | G | delta | tail
    p1=wk+6-5*s; p2=wk+Qw[r%7]
    Gv=np.array(G,dtype=np.uint8)
    out=np.where(d<p1,A(ga),np.where(d<p2,A(de),T))
    m=(d>=p1)&(d<p1+14)
    out[m]=Gv[d[m]-p1]
    return out

def learn_tables(R,al,be,ga,de,ta,K=50):
    """glider word G, wall seams Pw (L) and Qw (R) from round K"""
    wk=w(K);gp=14*(K+3)
    Pw={};Qw={}
    for r in range(60,300):
        a=t(K)+r;row=R[a,:D]
        p1,p2=seams(row,a,r,K,al,be,ta,0)
        Pw.setdefault(r%7,p2-wk)
        assert Pw[r%7]==p2-wk
    G=None
    for r in range(12*K+60,gp-20):
        a=t(K)+r;row=R[a,:D]
        p1,_=seams(row,a,r,K,ga,de,ta,0)
        g="".join(".#"[x] for x in row[p1:p1+14])
        if G is None: G=g
        assert G==g
        # delta until tail
        q=p1+14
        while row[q]==de[(q-wk-5*r)%35]: q+=1
        Qw.setdefault(r%7,q-wk)
        assert Qw[r%7]==q-wk,(r,Qw[r%7],q-wk)
    return [1 if c=="#" else 0 for c in G],[Pw[i] for i in range(7)],[Qw[i] for i in range(7)]

if __name__=="__main__":
    kmin=int(sys.argv[1]) if len(sys.argv)>1 else 3
    kmax=int(sys.argv[2]) if len(sys.argv)>2 else 54
    R=load()
    al,be,ga,de,ta=learn(R)
    G,Pw,Qw=learn_tables(R,al,be,ga,de,ta)
    print("alpha",ws(al));print("beta ",ws(be));print("gamma",ws(ga));print("delta",ws(de))
    print("G","".join(".#"[x] for x in G),"Pw",Pw,"Qw",Qw)
    for j in range(7): print("tail",j,"".join(".#"[ta[(j,e)]] for e in range(10)))
    E=[1 if c=='#' else 0 for c in '...#...#......#..#......#..#......#..#......#..#..']
    W=(al,be,ga,de,ta,G,Pw,Qw,E)
    bad=Counter(); tot=Counter(); firstbad={}
    for k in range(kmin,kmax+1):
        for r in range(0,14*(k+3)):
            a=t(k)+r
            if a>=len(R): continue
            n=min(D,len(R[0])-16)
            m=gen_row(k,r,W,n)
            true=R[a,:n]
            ph="L" if r<12*k+32 else "R"
            tot[ph]+=1
            if not (true==m).all():
                s=14*(k+3)-r
                key=(ph, r if ph=="L" and r<8 else ("s",s) if (ph=="R" and (s<=3 or s>=2*k+8)) else ("mid",))
                bad[key]+=1
                firstbad.setdefault(key,(k,r))
    print("rows",dict(tot),"mismatching rows by class",dict(bad), "total",sum(bad.values()))
