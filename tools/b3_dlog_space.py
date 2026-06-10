"""
Angle B3 -- reachability in DLOG COORDINATES (the right state space).

Facts that collapse the state space:
 * c mod 9  <=>  dlog mod 6  (since 2 has order 6 mod 9; 2^(d mod 6) mod 9 = c mod 9).
   => tau(c) is a function of (dlog c mod 6).
 * one-edge v->v' at level j (modulus 3^(R+j)):  dlog(c') = dlog(c) - tau(c')  (mod ord),
   and tau(c') is read from c'%9 = (dlog(c)-tau(c')) mod 6 -- a self-consistency that
   selects the admissible targets.  So one-edges are EXPLICIT dlog shifts.
 * zero-edge v->v' (j->j+1):  c -> 3c+1 then divide;  dlog at level j+1 of (3c+1) is
   dlog_{j+1}(c)-translated by the affineDlogJump (depends on full c, the OPEN part),
   then the target dlog(c') = dlog_{j+1}(3c+1) - tau(c').

We KEEP exact c as the witness (cheap), but answer the reachability purely about the
dlog value at each vertex's own full level.  The state for the clean/dirty product is
(j, c).  We report the SET of reachable dlog values at each j, exhaustively where the
slice is finite.

KEY EXPERIMENT: restrict zero-budget Q.  With Q fixed, j in [0,Q].  At each j the
reachable c live in 3^(R+j) but the reachable dlog VALUES may be a small set.  We
exhaust the dlog-value reachable set per j and test:
   does dlog=2 ever appear, and is dlog=0 (goal) an unavoidable predecessor?
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202
from collections import deque

def tau_from_dlog_mod6(d):
    # c mod 9 = 2^(d mod 6) mod 9
    c9 = pow(2, d % 6, 9)
    return TAU.get(c9, 0), c9

def one_edge_dlog_targets(d, R, j):
    """From a vertex with dlog d (at level R+j), the admissible one-edge targets'
    dlog values.  For each candidate alpha in X with tau=tau(alpha): target dlog
    d' = d - tau (mod ord); admissible iff (d') gives c'%9 == alpha, i.e.
    2^(d' mod 6) mod 9 == alpha."""
    ord_ = 2*3**(R+j-1)
    res=[]
    for a in sorted(X):
        t=TAU[a]
        dp=(d - t) % ord_
        if pow(2, dp%6, 9) == a:
            res.append((dp, t, a))
    return res

def outgoing_exact(R, Q, j, c):
    out=[]
    M=3**(R+j)
    for a in sorted(X):
        t=TAU[a]; inv2t=pow(pow(2,t,M),-1,M); cp=(inv2t*c)%M
        if cp%9==a: out.append((j,cp,t,'one'))
    if j<Q:
        Mp=3**(R+j+1)
        for a in sorted(X):
            t=TAU[a]; inv2t=pow(pow(2,t,Mp),-1,Mp); cp=(inv2t*((3*c+1)%Mp))%Mp
            if cp%9==a: out.append((j+1,cp,t-2,'zero'))
    return out

def dlogv(R,j,c):
    K=R+j; return fast_dlog(c%3**K,K)

def reachable_dlog_per_j(m, Q, max_states=2_000_000):
    """Exhaust reachable (j,c) for j in [0,Q]; collect reachable dlog values per j,
    and whether dlog==2 is reached strictly before any dlog==0 (goal) on a path.
    Dedup by (j, dlog) to keep it finite-ish per level (one-edge orbit at fixed j
    is a coset; zero-edges add finitely many)."""
    R=22*m+2
    start_c=aS202()%3**R
    sd=dlogv(R,0,start_c)
    # product (j, dvalue, hit0flag) ; we use dvalue as the dedup key (with exact c
    # carried for zero-edge affine computation -- store one representative c per d).
    seen=set()
    rep={}  # (j,d)->c representative
    start_flag=(sd==0)
    s0=(0,sd,start_flag)
    seen.add(s0); rep[(0,sd)]=start_c
    dq=deque([s0])
    dlog_by_j={jj:set() for jj in range(Q+1)}
    reached2_clean=None; reached2_dirty=None; goal_reached=set()
    n=0
    while dq and n<max_states:
        j,d,flag=dq.popleft(); n+=1
        dlog_by_j[j].add(d)
        if d==0: goal_reached.add(j)
        if d==2:
            if not flag and reached2_clean is None: reached2_clean=(j,)
            elif flag and reached2_dirty is None: reached2_dirty=(j,)
        c=rep[(j,d)]
        for (j2,c2,om,kind) in outgoing_exact(R,Q,j,c):
            d2=dlogv(R,j2,c2)
            f2=flag or (d2==0)
            key=(j2,d2,f2)
            if key not in seen:
                seen.add(key)
                if (j2,d2) not in rep: rep[(j2,d2)]=c2
                dq.append((j2,d2,f2))
    return dict(states=n, exhausted=(len(dq)==0),
                dlog_by_j={jj:sorted(s) for jj,s in dlog_by_j.items()},
                reached2_clean=reached2_clean, reached2_dirty=reached2_dirty,
                goal_reached=sorted(goal_reached))

if __name__=="__main__":
    m=1; R=22*m+2
    print(f"=== dlog-coordinate reachable set, m={m}, R={R} ===")
    print(f" start dlog d0={dlogv(R,0,aS202()%3**R)}, ord_R={2*3**(R-1)}")
    for Q in [1,2,3,4,5,6]:
        r=reachable_dlog_per_j(m,Q,max_states=3_000_000)
        print(f"\n Q={Q}: states={r['states']} exhausted={r['exhausted']}")
        print(f"   dlog2 clean={r['reached2_clean']} dirty={r['reached2_dirty']} "
              f"goal_j={r['goal_reached']}")
        for jj in range(Q+1):
            dl=r['dlog_by_j'][jj]
            small=[x for x in dl if x<20]
            print(f"   j={jj}: #dlog={len(dl)} small_vals(<20)={small} has2={2 in dl} has0={0 in dl}")
