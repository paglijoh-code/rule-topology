import numpy as np, os, tempfile
S=os.environ.get("SQ_TMP",tempfile.gettempdir())+os.sep
N=int(os.environ.get("SQ_N",24000));D=int(os.environ.get("SQ_D",800))
FN=os.environ.get("SQ_FILE",S+"R.bin")
def load(fn=None,N=N,D=D):
    fn=fn or FN
    return np.fromfile(fn,dtype=np.uint8).reshape(N,D+16)
t=lambda k:7*k*k+35*k+13
w=lambda k:35+10*k
def pre(R,a,D=D):
    r=R[a,:D]; p=D-10
    while p>0 and r[p-1]==r[p-1+10]: p-=1
    return p
