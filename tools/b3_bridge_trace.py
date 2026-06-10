"""
Angle B3 -- THE ZERO-EDGE BRIDGE from the c==1 mod 9 start, traced at high precision.

The start has c = aS202 = 1+3^22, dlog d0 == 0 (mod 2*3^21) but != 0 (mod 2*3^22).
It has NO one-edge (c==1 mod9, N2).  So the FIRST edge is a zero-edge.  We trace the
actual dlog evolution at FULL precision (level large), tracking for each reachable
vertex (j,c):
   dlog_full = dlog at level 22*(m+1)+2 + j   (working, residual m=1 -> Rwork=46)
   dlog_coarse = dlog at level 22*m+2 + j      (coarse  = 24 + j)
and the two key residues:
   trap (working): dlog_full == 2     <-> source can deep-jump to working goal
   coarse-precise: dlog_coarse == 0    <-> c==1 mod 3^(24+j)
We do a constrained BFS at FULL working precision but dedup by (j, c mod 3^(Rwork+j)),
exploring small Q, and record whether dlog_coarse==2 (trap projection) is reached
strictly before dlog_coarse==0.

Because the start's coarse dlog d0_coarse == dlog(aS202 mod 3^24) at level 24, and
aS202==1+3^22 so aS202 == 1 (mod 3^22): d0_coarse == 0 (mod 2*3^21) but != 0 mod 2*3^23.
So start is NOT coarse-precise.  Good.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202
from collections import deque

def dlogv(c,k): return fast_dlog(c%3**k,k)

def outgoing(R,Q,j,c):
    out=[]; M=3**(R+j)
    for a in sorted(X):
        t=TAU[a]; inv=pow(pow(2,t,M),-1,M); cp=(inv*c)%M
        if cp%9==a: out.append((j,cp,t,'one'))
    if j<Q:
        Mp=3**(R+j+1)
        for a in sorted(X):
            t=TAU[a]; inv=pow(pow(2,t,Mp),-1,Mp); cp=(inv*((3*c+1)%Mp))%Mp
            if cp%9==a: out.append((j+1,cp,t-2,'zero'))
    return out

def run(residual_m, Q, max_states=400000):
    Rw=22*(residual_m+1)+2     # working
    Rc=22*residual_m+2          # coarse
    start_c=aS202()%3**Rw
    d0c=dlogv(start_c,Rc)
    def coarse_dlog(j,c): return dlogv(c, Rc+j)
    def working_dlog(j,c): return dlogv(c, Rw+j)
    start_flag=(coarse_dlog(0,start_c)==0)
    seen=set([(0,start_c,start_flag)]); dq=deque([(0,start_c,start_flag)])
    n=0
    cl_trap=None; di_trap=None; cl_count=0; coarse0_examples=[]
    # also track: among CLEAN states, what coarse-dlog values appear
    clean_cdlogs=set()
    while dq and n<max_states:
        j,c,flag=dq.popleft(); n+=1
        cd=coarse_dlog(j,c)
        if not flag: clean_cdlogs.add(cd)
        if cd==2:
            if not flag and cl_trap is None: cl_trap=(j, working_dlog(j,c))
            elif flag and di_trap is None: di_trap=(j,)
        for (j2,c2,om,kind) in outgoing(Rw,Q,j,c):
            cd2=coarse_dlog(j2,c2)
            f2=flag or (cd2==0)
            if f2 and not flag and len(coarse0_examples)<5:
                coarse0_examples.append((j2, kind, cd2))
            if f2 and not flag: cl_count+=1
            key=(j2,c2,f2)
            if key not in seen:
                seen.add(key); dq.append((j2,c2,f2))
    return dict(states=n, exhausted=(len(dq)==0), Rw=Rw, Rc=Rc, d0c=d0c,
                cl_trap=cl_trap, di_trap=di_trap, coarse0_hits=cl_count,
                clean_cdlogs_small=sorted(x for x in clean_cdlogs if x<30),
                clean_cdlogs_count=len(clean_cdlogs),
                coarse0_examples=coarse0_examples)

if __name__=="__main__":
    rm=1
    print(f"=== zero-edge bridge, residual m={rm}: Rwork={22*(rm+1)+2}, Rcoarse={22*rm+2} ===")
    d0c=dlogv(aS202()%3**(22*(rm+1)+2), 22*rm+2)
    print(f" start coarse dlog d0c = {d0c}  (==0 mod 2*3^21? {d0c%(2*3**21)==0}; ==0 mod 2*3^23? {d0c%(2*3**23)==0})")
    for Q in [1,2,3,4,6,8,10]:
        r=run(rm,Q,max_states=250000)
        print(f"\n Q={Q}: states={r['states']} exh={r['exhausted']}")
        print(f"   trap(coarse-dlog=2) clean={r['cl_trap']} dirty={r['di_trap']}")
        print(f"   coarse-precise(dlog=0) hits among clean-frontier={r['coarse0_hits']}; "
              f"examples(j,kind,cd)={r['coarse0_examples']}")
        print(f"   clean coarse-dlog values<30: {r['clean_cdlogs_small']} (total distinct {r['clean_cdlogs_count']})")
