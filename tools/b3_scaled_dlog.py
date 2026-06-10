"""
Angle B3 -- SCALED faithful model in DLOG COORDINATES (exact, exhaustive).

State = (j, d) where d = dlog_{Rw+j}(c) in Z/ord(Rw+j), ord(k)=2*3^(k-1).
This is a bijection with the vertex (j, c mod 3^(Rw+j)).

Transitions (all deterministic functions of (j,d), verified by determinacy):
  one-edge (same j):  for admissible alpha in X, d' = d - tau(alpha) (mod ord(Rw+j)),
     valid iff 2^(d' mod 6) mod 9 == alpha.
  zero-edge (j->j+1): let c = 2^d mod 3^(Rw+j); compute m1 = (3c+1) mod 3^(Rw+j+1);
     dm = dlog_{Rw+j+1}(m1); then for admissible alpha: d' = dm - tau(alpha) (mod ord(Rw+j+1)),
     valid iff 2^(d' mod6) mod9==alpha.  (Need j<Q.)

Trap / goal conditions, in dlog at the relevant precision:
  WORKING trap : dlog_{Rw+j}(c) == 2.   (== d == 2)
  COARSE-precise: dlog_{Rc+j}(c) == 0, i.e. d == 0 (mod ord(Rc+j))  [reduce d mod ord(Rc+j)]
  COARSE trap   : dlog_{Rc+j}(c) == 2, i.e. (d mod ord(Rc+j)) == 2.

Start: A = 1+3^g, c0 = A mod 3^Rw, d0 = dlog_{Rw}(c0).
Constraint: reach WORKING trap (d==2) WITHOUT first hitting a COARSE-precise vertex.
Product (j,d,flag).  EXHAUSTIVE because we dedup by (j,d,flag) and j<=Q.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X
from collections import deque

def ordk(k): return 2*3**(k-1)
def dlogv(c,k): return fast_dlog(c%3**k,k)

def decide_scaled_dlog(g, b, Q, m=1, max_states=5_000_000):
    Rw = g*(m+1)+b
    Rc = g*m+b
    A = 1+3**g
    c0 = A % 3**Rw
    if c0 % 9 not in X:
        return dict(skip=True, reason=f"start c%9={c0%9} not admissible")
    d0 = dlogv(c0, Rw)
    def coarse_d(j, d):
        # d is dlog at level Rw+j; reduce to coarse level Rc+j
        return d % ordk(Rc+j)
    start_flag = (coarse_d(0,d0)==0)
    seen=set([(0,d0,start_flag)]); dq=deque([(0,d0,start_flag)])
    n=0
    wtc=False; wtd=False; ctc=False; c0reached=False; wg=False
    while dq and n<max_states:
        j,d,flag=dq.popleft(); n+=1
        if wtc:  # early out: we found a clean route to the working trap
            break
        cd=coarse_d(j,d)
        if cd==0: c0reached=True
        if d==0: wg=True
        if d==2:
            if not flag: wtc=True
            else: wtd=True
        if cd==2:
            if not flag: ctc=True
        K=Rw+j; M=3**K; O=ordk(K)
        # one-edges
        for a in sorted(X):
            ta=TAU[a]; dp=(d-ta)%O
            if pow(2, dp%6, 9)==a:
                cd2=dp % ordk(Rc+j)
                f2=flag or (cd2==0)
                key=(j,dp,f2)
                if key not in seen: seen.add(key); dq.append(key)
        # zero-edges
        if j<Q:
            K2=Rw+j+1; M2=3**K2; O2=ordk(K2)
            c=pow(2,d,M)                 # c mod 3^K  (== vertex c at this precision)
            m1=(3*c+1)%M2
            dm=dlogv(m1,K2)
            for a in sorted(X):
                ta=TAU[a]; dp=(dm-ta)%O2
                if pow(2, dp%6, 9)==a:
                    cd2=dp % ordk(Rc+j+1)
                    f2=flag or (cd2==0)
                    key=(j+1,dp,f2)
                    if key not in seen: seen.add(key); dq.append(key)
    return dict(g=g,b=b,Q=Q,m=m,Rw=Rw,Rc=Rc,d0=d0,states=n,exhausted=(len(dq)==0),
                work_trap_clean=wtc, work_trap_dirty=wtd, coarse_trap_clean=ctc,
                coarse0=c0reached, work_goal=wg)

if __name__=="__main__":
    print("=== SCALED faithful model in dlog coords (EXHAUSTIVE) ===")
    print(" g=gap, b=base, m=1. WTC=work-trap-clean WTD=work-trap-dirty")
    print(" CTC=coarse-trap-clean C0=coarse-precise-reached WG=work-goal")
    rows=[]
    for (g,b) in [(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(2,3)]:
        for Q in [2,3,4,5,6]:
            r=decide_scaled_dlog(g,b,Q,m=1,max_states=600_000)
            if r.get('skip'):
                print(f" g={g} b={b}: SKIP {r['reason']}"); break
            tag="EXH" if r['exhausted'] else "CAP"
            print(f" g={g} b={b} Q={Q:>2} [{tag}] Rw={r['Rw']} Rc={r['Rc']} d0={r['d0']}: "
                  f"WTC={int(r['work_trap_clean'])} WTD={int(r['work_trap_dirty'])} "
                  f"CTC={int(r['coarse_trap_clean'])} C0={int(r['coarse0'])} WG={int(r['work_goal'])} st={r['states']}")
        print()
