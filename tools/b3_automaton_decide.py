"""
Angle B3 -- DECIDE trap reachability via the deterministic dlog-digit automaton.

PROVEN-by-computation determinacy: J(c,j) mod 2*3^t depends only on c mod 3^(t+1),
equivalently on d = dlog(c) mod 2*3^t.  So the inverse dynamics descends to a
WELL-DEFINED automaton on  Z/(2*3^t)  in dlog coordinates, for every truncation t.

Edges (both descend mod 2*3^t by dlog_reduce, valid once R+j-1 >= t):
  one-edge:  d -> d - tau(alpha)              (alpha admissible: 2^((d-tau) mod 6)%9==alpha)
  zero-edge: d -> d + J(d) - tau(alpha)        (J(d) = affine jump as fn of d mod 2*3^t)
We precompute J(d) mod 2*3^t for all d (via a representative c=2^d at a high enough level).

We then ask, at truncation t (so 'd==2' means d ≡ 2 (mod 2*3^t) -- a NECESSARY
condition for the real trap dlog=2):
   starting from d0 = dlog(aS202) mod 2*3^t, is residue 2 reachable in the automaton
   WITHOUT first visiting residue 0 (the goal / coarse-precise class) ?
Product automaton over (d, hit0) with d in Z/(2*3^t).  Finite, exhaustively decided.

If for some t the answer is NO -> the real trap is UNREACHABLE-clean -> residual holds.
If for all tested t the answer is YES -> no obstruction at these truncations (the
necessary condition is satisfied; trap may be reachable).  We also track whether the
zero-edge BUDGET matters: we allow unlimited j (Q=inf) since truncation hides j.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202
from collections import deque

def dlogv(c,k): return fast_dlog(c%3**k,k)

def build_J_table(t, level=None):
    """J(d) mod 2*3^t for all d in Z/(2*3^t).  Use a representative c=2^d at level
    'level' >= t+2 (enough precision), compute J=dlog(3c+1)-dlog(c) mod 2*3^t."""
    N=2*3**t
    if level is None: level=t+3
    M=3**level
    Jtab=[0]*N
    for d in range(N):
        c=pow(2,d,M)              # 2^d mod 3^level ; its dlog mod 2*3^t is d (consistent)
        if c%3==0:                # never, 2^d is a unit
            continue
        J=(dlogv(3*c+1,level)-dlogv(c,level))%N
        Jtab[d]=J
    return Jtab,N

def tau_of_d(d):
    c9=pow(2,d%6,9); return TAU.get(c9,0), c9

def automaton_edges(d, N, Jtab, allow_zero=True):
    """successor dlog residues (mod N) from d. one-edges always; zero-edges if allowed."""
    succ=[]
    # one-edges
    for a in sorted(X):
        ta=TAU[a]; dp=(d-ta)%N
        if pow(2, dp%6, 9)==a:
            succ.append(('one',dp,ta))
    # zero-edges
    if allow_zero:
        J=Jtab[d%N]
        base=(d+J)%N
        for a in sorted(X):
            ta=TAU[a]; dp=(base-ta)%N
            if pow(2, dp%6, 9)==a:
                succ.append(('zero',dp,ta-2))
    return succ

def decide(t, allow_zero=True, level=None):
    Jtab,N=build_J_table(t, level=level)
    R=22*1+2  # residual m=1 base for d0; (for higher m, d0 changes but the automaton same)
    d0=dlogv(aS202()%3**(R), R)%N
    # product (d, hit0)
    start_flag=(d0%N==0)
    seen=set([(d0,start_flag)])
    dq=deque([(d0,start_flag)])
    reach2_clean=False; reach2_dirty=False; reach0=False
    pred_of2=None
    while dq:
        d,flag=dq.popleft()
        if d==2:
            if not flag: reach2_clean=True
            else: reach2_dirty=True
        if d==0: reach0=True
        for (kind,dp,om) in automaton_edges(d,N,Jtab,allow_zero=allow_zero):
            f2=flag or (dp==0)
            key=(dp,f2)
            if key not in seen:
                seen.add(key); dq.append(key)
    return dict(t=t,N=N,d0=d0, reach2_clean=reach2_clean, reach2_dirty=reach2_dirty,
                reach0=reach0, nstates=len(seen))

if __name__=="__main__":
    print("=== DECIDE: dlog automaton mod 2*3^t, trap residue=2, goal residue=0 ===")
    print("  (d0 = dlog(aS202) mod 2*3^t, residual m=1)")
    for t in range(1,8):
        r=decide(t, allow_zero=True)
        print(f" t={t} N={r['N']:>7} d0={r['d0']:>7}: "
              f"reach2_clean={r['reach2_clean']} reach2_dirty={r['reach2_dirty']} "
              f"reach0={r['reach0']} |states|={r['nstates']}")
    print()
    print("=== same, but ONE-EDGES ONLY (zero budget Q=0 after start; pure one-edge orbit) ===")
    for t in range(1,8):
        r=decide(t, allow_zero=False)
        print(f" t={t} N={r['N']:>7} d0={r['d0']:>7}: reach2_clean={r['reach2_clean']} "
              f"reach0={r['reach0']} |states|={r['nstates']}")
