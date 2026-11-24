#!/usr/bin/env python3
"""Spot test: which push pairs (S1, S2) have a sqrt-like wall?  Uses bf2.c (independent brute force).
For each pair: tail period p of the row, pre(a) (start of the periodic tail), block maxima of pre over
a-windows, exponent e of  w ~ a^e  between a~1000 and a~4500.  e~0.5 with several jumps is the sqrt signature.
Usage: spot.py N S1csv S2csv   |   spot.py --scan"""
import sys, os, tempfile, subprocess, itertools, numpy as np, json
HERE=os.path.dirname(os.path.abspath(__file__))
S=os.environ.get("SQ_TMP",tempfile.gettempdir())+os.sep
BF=S+"bf2_bin"
def build():
    subprocess.check_call(["cc","-O2","-o",BF,os.path.join(HERE,"..","bf2.c")])
def table(N,S1,S2):
    out=S+"spot_tab.bin"
    subprocess.check_call([BF,str(N),",".join(map(str,S1)),",".join(map(str,S2)),out])
    return np.memmap(out,dtype=np.uint8,mode="r",shape=(N+1,N+1))
def pre_of(row,pmax=140):
    n=len(row)
    for p in range(1,pmax+1):
        tail=row[n-4*pmax-p:]
        if (tail[:-p]==tail[p:]).all():
            eq=row[:-p]==row[p:]
            bad=np.nonzero(~eq)[0]
            return p,(int(bad[-1])+1 if len(bad) else 0)
    return None,None
def analyse(N,S1,S2):
    B=table(N,S1,S2)
    res=[]
    A=list(range(100,N//2,25))
    pres=[];ps=set()
    for a in A:
        p,pr=pre_of(np.array(B[a,a:]))
        if p is None: return {"S1":S1,"S2":S2,"err":"no period"}
        ps.add(p); pres.append(pr)
    pres=np.array(pres); A=np.array(A)
    def wmax(lo,hi): m=(A>=lo)&(A<hi); return int(pres[m].max())
    w1=wmax(900,1100); w2=wmax(N//2-400,N//2)
    a1=1000.; a2=N//2-200.
    e=np.log(max(w2,1)/max(w1,1))/np.log(a2/a1)
    # jump record: running max of block-max in blocks of 100 rows
    blocks=[(int(lo),wmax(lo,lo+100)) for lo in range(100,N//2-100,100)]
    steps=[b for i,b in enumerate(blocks[1:],1) if b[1]!=blocks[i-1][1]]
    return {"S1":S1,"S2":S2,"periods":sorted(ps),"w1000":w1,"wend":w2,"exp":round(float(e),3),"nsteps":len(steps)}
if __name__=="__main__":
    build()
    if sys.argv[1]=="--scan":
        N=int(sys.argv[2]); outf=sys.argv[3]
        S2s=[[1,2],[1,2,3],[1,2,3,4],[1,2,3,4,5],[1,2,3,4,5,6]]
        with open(outf,"w") as f:
            for m in (3,4,5):
                for S1 in itertools.combinations(range(1,8),m):
                    if max(S1)<4: continue
                    for S2 in S2s:
                        r=analyse(N,list(S1),S2); f.write(json.dumps(r)+"\n"); f.flush()
    else:
        N=int(sys.argv[1]); print(analyse(N,list(map(int,sys.argv[2].split(","))),list(map(int,sys.argv[3].split(",")))))
