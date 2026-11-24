from common import *
def runs(R,a,P=35,minlen=0,lim=None):
    """maximal intervals [i,j) with row[d]=row[d+P] for d in [i,j-P) i.e. P-periodic runs of length j-i>=P+minlen"""
    r=R[a,:lim or (w_est(R,a)+P)]
    n=len(r); out=[]; i=0
    eq=[r[d]==r[d+P] for d in range(n-P)]
    d=0
    while d<len(eq):
        if eq[d]:
            e=d
            while e<len(eq) and eq[e]: e+=1
            out.append((d,e+P))
            d=e
        else: d+=1
    return out
def w_est(R,a): return pre(R,a)+10
