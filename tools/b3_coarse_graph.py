"""
Angle B3 -- THE REDUCTION TO THE COARSE m-LEVEL GRAPH.

Claim (projection argument): the working (m+1)-inverse-graph projects, via
projpi_m (c |-> c mod 3^(22m+2+j)), onto the m-inverse-graph, sending:
  - InvStart(m+1)  -> InvStart(m)              [projpi_InvStart, PROVEN]
  - admissible edge -> admissible edge          [consistency mod 3^(Rwork+j) => mod 3^(Rcoarse+j)]
  - trap c==4 (work full prec) -> c==4 (coarse full prec) = dlog_coarse 2  [4 < 3^Rcoarse]
  - coarse-precise (c==1 mod 3^(Rcoarse+j)) -> goal of the m-graph (dlog_coarse 0)

THEREFORE a NECESSARY condition for the working trap to be reachable WITHOUT a
prior coarse-precise vertex is:  in the m-graph, the residue c==4 (dlog 2 at full
m-precision) is reachable from InvStart(m) WITHOUT first hitting a goal (c==1).

So we DECIDE this necessary condition in the m-graph (R = 22m+2).  If it FAILS
(every route to dlog 2 goes through dlog 0 first), the working trap is unreachable
-> FirstMPrecisionSuffixPositive HOLDS.

Here m is the *residual* m (>=1); R = 22m+2.  Residual m=1 -> R=24.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202
from collections import deque

def outgoing(R, Q, j, c):
    out = []
    M = 3**(R+j)
    for a in sorted(X):
        t = TAU[a]
        inv2t = pow(pow(2, t, M), -1, M)
        cp = (inv2t * c) % M
        if cp % 9 == a:
            out.append((j, cp, t, 'one'))
    if j < Q:
        Mp = 3**(R+j+1)
        for a in sorted(X):
            t = TAU[a]
            inv2t = pow(pow(2, t, Mp), -1, Mp)
            cp = (inv2t * ((3*c+1) % Mp)) % Mp
            if cp % 9 == a:
                out.append((j+1, cp, t-2, 'zero'))
    return out

def dlog_full(R, j, c):
    K = R + j
    return fast_dlog(c % 3**K, K)

def search_coarse(m, Q, max_states=500000, track_paths=False):
    """In the m-graph (R=22m+2): is dlog_full == 2 reachable from InvStart(m)
    WITHOUT first hitting dlog_full == 0 (a goal)?
    Product automaton over (j,c, hit_goal_flag)."""
    R = 22*m + 2
    start_c = aS202() % 3**R           # == 1+3^22 for m=1
    sd = dlog_full(R,0,start_c)
    start_flag = (sd == 0)
    seen = set([(0,start_c,start_flag)])
    dq = deque([(0,start_c,start_flag, [(0,start_c,sd)])] if track_paths
               else [(0,start_c,start_flag)])
    n=0
    reached2_clean=None; reached2_dirty=None; goal_hits=0
    dlogvals=set()
    while dq and n<max_states:
        item = dq.popleft(); n+=1
        if track_paths:
            j,c,flag,path = item
        else:
            j,c,flag = item; path=None
        d = dlog_full(R,j,c); dlogvals.add(d)
        if d == 2:
            if not flag and reached2_clean is None:
                reached2_clean=(j,c,path)
            elif flag and reached2_dirty is None:
                reached2_dirty=(j,c)
        for (j2,c2,om,kind) in outgoing(R,Q,j,c):
            d2 = dlog_full(R,j2,c2)
            f2 = flag or (d2==0)
            if f2 and not flag: goal_hits+=1
            if track_paths:
                key=(j2,c2,f2)
                if key not in seen:
                    seen.add(key); dq.append((j2,c2,f2, path+[(j2,c2,d2)]))
            else:
                key=(j2,c2,f2)
                if key not in seen:
                    seen.add(key); dq.append((j2,c2,f2))
    return dict(states=n, reached2_clean=reached2_clean, reached2_dirty=reached2_dirty,
                goal_hits=goal_hits, exhausted=(len(dq)==0),
                dlogvals=sorted(dlogvals)[:30], distinct_dlog=len(dlogvals))

if __name__ == "__main__":
    print("=== COARSE m-graph reachability of dlog=2 (the trap projection) ===")
    for m in [1]:
        R=22*m+2
        sc = aS202()%3**R
        print(f"-- residual m={m}, R={R}, start c={sc}, dlog_start={dlog_full(R,0,sc)} --")
        for Q in [1,2,3,4,5,6,8,10,12]:
            r=search_coarse(m,Q,max_states=300000)
            print(f" Q={Q}: states={r['states']} exh={r['exhausted']} "
                  f"dlog2_clean={'YES '+str(r['reached2_clean'][:2]) if r['reached2_clean'] else 'no'} "
                  f"dlog2_dirty={'yes' if r['reached2_dirty'] else 'no'} "
                  f"goal_hits={r['goal_hits']} #dlog={r['distinct_dlog']}")
