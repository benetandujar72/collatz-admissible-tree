"""
Angle B3 -- SCALED-DOWN faithful model, exhaustively decidable.

The real problem: aS202 = 1 + 3^22, Rcoarse = 22*m+2, Rwork = 22*(m+1)+2, gap 22.
We build a faithful analog with the constant '22' replaced by a small g (the
'gap/valuation'), and the '+2' replaced by a small base b:
   start constant  A := 1 + 3^g
   Rcoarse := g*m + b   (we take m=1 -> Rcoarse = g + b)
   Rwork   := g*(m+1)+b = 2g + b
   trap (working): working-dlog == 2  (deep one-edge to working goal)
   coarse-precise: coarse-dlog == 0   (c == 1 mod 3^(Rcoarse+j))
   coarse-trap    : coarse-dlog == 2   (projection of working trap)

The inverse graph uses the SAME tau table and edge laws (they are universal).
We EXHAUSTIVELY BFS at full working precision (small now) with zero-budget Q, and
decide:  is the working trap reachable WITHOUT first hitting a coarse-precise vertex?
We also decide the coarse necessary condition.

Because everything is small, we get a definitive yes/no per (g,b,Q,m).
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X
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

def decide_scaled(g, b, Q, m=1, max_states=3_000_000):
    """Faithful scaled model. Returns reachability verdicts."""
    A = 1 + 3**g
    Rw = g*(m+1) + b
    Rc = g*m + b
    if A % 9 not in X:   # need start admissible (A%9 must be in X). A=1+3^g; A%9=1 if g>=2.
        pass
    start_c = A % 3**Rw
    def cdl(j,c): return dlogv(c, Rc+j)
    def wdl(j,c): return dlogv(c, Rw+j)
    # sanity: start admissible?
    start_adm = (start_c % 9) in X
    start_flag = (cdl(0,start_c)==0)
    seen=set([(0,start_c,start_flag)]); dq=deque([(0,start_c,start_flag)])
    n=0
    work_trap_clean=False; work_trap_dirty=False
    coarse_trap_clean=False; coarse_trap_dirty=False
    coarse0_reached=False
    work_goal_reached=False
    while dq and n<max_states:
        j,c,flag=dq.popleft(); n+=1
        cd=cdl(j,c); wd=wdl(j,c)
        if cd==0: coarse0_reached=True
        if wd==0: work_goal_reached=True
        if wd==2:
            if not flag: work_trap_clean=True
            else: work_trap_dirty=True
        if cd==2:
            if not flag: coarse_trap_clean=True
            else: coarse_trap_dirty=True
        for (j2,c2,om,kind) in outgoing(Rw,Q,j,c):
            cd2=cdl(j2,c2)
            f2=flag or (cd2==0)
            key=(j2,c2,f2)
            if key not in seen:
                seen.add(key); dq.append((j2,c2,f2))
    return dict(g=g,b=b,Q=Q,m=m,Rw=Rw,Rc=Rc,states=n,exhausted=(len(dq)==0),
                start_adm=start_adm,
                work_trap_clean=work_trap_clean, work_trap_dirty=work_trap_dirty,
                coarse_trap_clean=coarse_trap_clean, coarse_trap_dirty=coarse_trap_dirty,
                coarse0=coarse0_reached, work_goal=work_goal_reached)

if __name__=="__main__":
    print("=== SCALED faithful model: does the constraint EVER block the trap? ===")
    print(" g=gap(analog of 22), b=base(analog of 2), m=1.")
    print(" WTC=work-trap-clean WTD=work-trap-dirty CTC=coarse-trap-clean C0=coarse0-reached WG=work-goal")
    for (g,b) in [(2,2),(3,2),(4,2),(2,1),(3,1),(2,3),(3,3),(4,1),(5,1),(2,0),(3,0)]:
        for Q in [2,3,4,6,8]:
            r=decide_scaled(g,b,Q,m=1,max_states=2_000_000)
            tag = "EXH" if r['exhausted'] else "cap"
            print(f" g={g} b={b} Q={Q} [{tag}] Rw={r['Rw']} Rc={r['Rc']} adm={r['start_adm']}: "
                  f"WTC={r['work_trap_clean']} WTD={r['work_trap_dirty']} "
                  f"CTC={r['coarse_trap_clean']} C0={r['coarse0']} WG={r['work_goal']} "
                  f"st={r['states']}")
        print()
