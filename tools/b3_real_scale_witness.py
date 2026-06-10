"""
DECISIVE TEST: construct a clean witness at the REAL scale (residual m=1: Rc=24, Rw=46),
or prove the constraint blocks it.  We use the mechanism discovered in the scaled model:
  (1) from the start (c==1 mod 9, no one-edge), take a zero-edge into c==7 mod 9;
  (2) run the 7<->4 one-edge ladder (and occasional class-1 to re-enable a zero-edge)
      to walk dlog DOWN toward 2, threading past every coarse-precise (coarse-dlog==0).

Rather than hand-craft, we do a GUIDED search at real working precision (Rw=46), but to
keep it tractable we DEDUP in dlog coords and use a greedy/best-first toward work_dlog -> 2
while the flag stays clean.  We also do an exhaustive check on the COARSE graph (Rc=24) in
DLOG coordinates with j bounded, because the coarse necessary condition is the bottleneck.

The coarse reachability of dlog 2 clean is the necessary condition; if it FAILS, barrier
holds.  If it SUCCEEDS, we then attempt to lift to a true working witness.

We work entirely in dlog coords using the deterministic transition (verified exact).
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202
from collections import deque
import heapq

def dlogv(c,k): return fast_dlog(c%3**k,k)
def ordk(k): return 2*3**(k-1)

def zero_target_dlog(d, K):
    """Given a vertex with dlog d at level K (c=2^d mod 3^K), the dlog at level K+1
    of (3c+1).  Deterministic."""
    M=3**K; M2=3**(K+1)
    c=pow(2,d,M)
    m1=(3*c+1)%M2
    return dlogv(m1,K+1)

def coarse_clean_search(g, b, m, Qmax, max_states=4_000_000):
    """COARSE graph (R=Rc), dlog coords: from start, can we reach dlog==2 WITHOUT
    hitting dlog==0 (goal) first?  State (j, d at level Rc+j, flag). j<=Qmax."""
    Rc=g*m+b; Rw=g*(m+1)+b
    A=1+3**g
    c0=A%3**Rc                 # PROJECT start to coarse
    d0=dlogv(c0,Rc)
    start_flag=(d0==0)
    start=(0,d0,start_flag)
    parent={start:None}; dq=deque([start]); n=0; target=None
    while dq and n<max_states:
        st=dq.popleft(); n+=1
        j,d,flag=st
        if (not flag) and d==2:
            target=st; break
        K=Rc+j; O=ordk(K)
        # one-edges
        for a in sorted(X):
            ta=TAU[a]; dp=(d-ta)%O
            if pow(2,dp%6,9)==a:
                f2=flag or (dp==0)
                ns=(j,dp,f2)
                if ns not in parent: parent[ns]=(st,('one',ta,a)); dq.append(ns)
        # zero-edges
        if j<Qmax:
            K2=Rc+j+1; O2=ordk(K2)
            dm=zero_target_dlog(d,K)
            for a in sorted(X):
                ta=TAU[a]; dp=(dm-ta)%O2
                if pow(2,dp%6,9)==a:
                    f2=flag or (dp==0)
                    ns=(j+1,dp,f2)
                    if ns not in parent: parent[ns]=(st,('zero',ta-2,a)); dq.append(ns)
    if target is None:
        return dict(found=False, states=n, exhausted=(len(dq)==0), Rc=Rc)
    # reconstruct
    path=[]; st=target
    while parent[st] is not None:
        prev,e=parent[st]; path.append((prev,e,st)); st=prev
    path.reverse()
    return dict(found=True, states=n, Rc=Rc, path=path, target=target)

if __name__=="__main__":
    print("=== COARSE-graph clean reachability of dlog=2 (necessary condition), dlog coords ===")
    print("    Real problem: g=22,b=2,m=1 -> Rc=24.  Also scan g to see the pattern.")
    for (g,b,m,Qmax) in [(22,2,1,6),(22,2,1,10),(2,2,1,6),(3,2,1,6),(4,2,1,8),
                          (5,2,1,8),(8,2,1,8),(12,2,1,8),(22,2,1,4)]:
        r=coarse_clean_search(g,b,m,Qmax,max_states=2_000_000)
        if r['found']:
            zlen=sum(1 for (_,e,_) in r['path'] if e[0]=='zero')
            print(f" g={g} b={b} m={m} Qmax={Qmax} Rc={r['Rc']}: CLEAN dlog=2 FOUND, "
                  f"path={len(r['path'])} edges ({zlen} zero), states={r['states']}")
        else:
            print(f" g={g} b={b} m={m} Qmax={Qmax} Rc={r['Rc']}: not found "
                  f"(exhausted={r['exhausted']}, states={r['states']})")
