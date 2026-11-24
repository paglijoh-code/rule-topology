#!/usr/bin/env python3
"""Compare the tile model against the independent C brute force bf2.c over EVERY cell a<=b<=N (rows a>=13).
Usage: verify_bf.py N   (builds bf2, writes (N+1)^2 bytes to the scratch dir)"""
import sys, os, tempfile, subprocess, numpy as np
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from model import *
N=int(sys.argv[1]); HERE=os.path.dirname(os.path.abspath(__file__))
bf=os.path.join(S,"bf2_bin"); out=os.path.join(S,"bf2_out.bin")
subprocess.check_call(["cc","-O2","-o",bf,os.path.join(HERE,"..","bf2.c")])
subprocess.check_call([bf,str(N),"1,2,5,6","1,2,3,4",out])
B=np.fromfile(out,dtype=np.uint8).reshape(N+1,N+1)
R=load()                         # learn the words from the K=50 round of the rowgen table
al,be,ga,de,ta=learn(R); G,Pw,Qw=learn_tables(R,al,be,ga,de,ta)
E=[1 if c=='#' else 0 for c in '...#...#......#..#......#..#......#..#......#..#..']
W=(al,be,ga,de,ta,G,Pw,Qw,E)
bad=0; cells=0
k=0
for a in range(t(0),N+1):
    while t(k+1)<=a: k+=1
    r=a-t(k); n=N-a+1
    m=gen_row(k,r,W,n); true=B[a,a:]
    cells+=n
    if not (m==true).all(): bad+=1
print("N",N,"rows",N+1-t(0),"cells",cells,"mismatching rows",bad)
