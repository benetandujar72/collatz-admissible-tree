"""
B1 -- Faithful forward reachability BFS in the inverse cylinder graph.

EXACT replica of InverseGraph.outgoingEdges (S215):
  invMod2(M)=(M+1)//2 ; invMod2Pow(t,M)=invMod2(M)^t % M
  one-edges: for alpha in X: tau=tau(alpha); y = invMod2Pow(tau,M)*v.c % M ; if y%9==alpha: edge (j, y) wt tau
  zero-edges (if j<Q): M'=3^(R+j+1); y=invMod2Pow(tau,M')*(3*v.c+1) % M'; if y%9==alpha: edge (j+1,y) wt tau-2

NOTE on direction: outgoingEdges enumerates INVERSE edges v->v'. The barrier path goes
InvStart(m) -> ... -> goal along these inverse edges. The trap T = {v.c == 4 mod 3^(R+j)} is the
SOURCE of a deep one-edge; in the forward (inverse-graph) search the trap is a VERTEX we may visit.

We do an EXHAUSTIVE BFS from InvStart over the inverse graph at R=22*M+2, recording:
  - whether any reachable vertex has c % 3^(R+j) == 4   (the trap, dlog=2)
  - the first m-precise vertex encountered (c == 1 mod 3^(R+j-22))  [coarse precision]
The CONSTRAINED question: is the trap reachable WITHOUT first hitting an m-precise vertex?
"""
import sys
from collections import deque
sys.path.insert(0,".")

def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
aS202=1+3**22

def invMod2(M): return (M+1)//2
def invMod2Pow(t,M): return pow(invMod2(M), t, M)

def outgoing(R, Q, j, c):
    """returns list of (j', c', weight). Exact replica."""
    out=[]
    M=3**(R+j)
    for a in X:
        t=tau(a)
        y=invMod2Pow(t,M)*c % M
        if y%9==a:
            out.append((j, y, t))
    if j<Q:
        Mp=3**(R+j+1)
        for a in X:
            t=tau(a)
            y=invMod2Pow(t,Mp)*(3*c+1) % Mp
            if y%9==a:
                out.append((j+1, y, t-2))
    return out

def coarse_precise(R, j, c):
    """m-precise: c == 1 mod 3^(R+j-22).  (R=22(m+1)+2, coarse level = 22m+2+j = R-22+j)."""
    lvl = R + j - 22
    if lvl < 1: return False
    return c % 3**lvl == 1 % 3**lvl

def is_trap(R, j, c):
    return c % 3**(R+j) == 4 % 3**(R+j)

def is_goal(R, j, c):
    return c % 3**(R+j) == 1 % 3**(R+j)

def bfs(M_idx, Q, maxstates=2_000_000, track_constraint=True):
    R = 22*M_idx + 2
    start_c = aS202 % 3**R
    start = (0, start_c)
    # State: (j, c). We track 'passed_precise' as part of state for the CONSTRAINED question.
    # constrained reachability: edges allowed only while not-yet-precise; once precise, stop expanding
    # (we want trap reachable strictly BEFORE any coarse-precise vertex).
    seen=set()
    dq=deque()
    # mark start precise? start is NOT m-precise (verified invStart_succ_not_mPrecise)
    sp = coarse_precise(R,0,start_c)
    dq.append((0,start_c)); seen.add((0,start_c))
    trap_hits=[]
    precise_hits=0
    first_precise_depth=None
    n=0
    while dq and n<maxstates:
        j,c=dq.popleft(); n+=1
        if is_trap(R,j,c):
            trap_hits.append((j,c))
            if len(trap_hits)<=5:
                pass
        prec = coarse_precise(R,j,c)
        if prec:
            precise_hits+=1
            if track_constraint:
                # CONSTRAINED: do not expand past a precise vertex (trap must come first)
                continue
        for (jp,cp,w) in outgoing(R,Q,j,c):
            if (jp,cp) not in seen:
                seen.add((jp,cp))
                dq.append((jp,cp))
    return dict(R=R, explored=n, seen=len(seen),
               trap_hits=len(trap_hits), trap_examples=trap_hits[:5],
               precise_hits=precise_hits, exhausted=(not dq))

if __name__=="__main__":
    for (Midx, Q, ms) in [(2,0,2_000_000),(2,1,2_000_000),(2,2,2_000_000),(2,3,1_500_000),(2,5,1_200_000)]:
        r=bfs(Midx,Q,maxstates=ms)
        print(f"M={Midx} (R={r['R']}) Q={Q}: explored={r['explored']} seen={r['seen']} "
              f"exhausted={r['exhausted']} TRAP_hits={r['trap_hits']} precise_hits={r['precise_hits']}")
        if r['trap_examples']:
            print("   trap examples (j,c):", r['trap_examples'])
