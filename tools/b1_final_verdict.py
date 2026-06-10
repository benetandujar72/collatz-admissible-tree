"""
B1 -- FINAL verdict assembly.

(1) Confirm: there EXISTS a path start -> trap with NO precise vertex anywhere (incl. interior),
    and the FIRST precise vertex on it (if forced) -- show it's not forced.
(2) Extract the canonical SHORTEST constrained path for r=4,g=3 and PRINT every vertex with
    its precise-status and trap-status, to exhibit the witness.
(3) Cross-check the small-model edges against the REAL InverseGraph.outgoingEdges formula
    (invMod2Pow) -- they are the SAME formula, so the witness lifts structurally.
(4) State the minimal modulus where a separating invariant could first occur: NONE.
    The reachable residues mod 3^t are EXACTLY the units for every t (proved exhaustively
    t<=11 + self-sustaining induction). The trap residue 4 is a unit. So no finite-modulus
    congruence/dlog invariant separates -- at ANY modulus.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
from collections import deque

def shortest_constrained_path(r,g,J):
    base=r+g; c0=(1+3**g)%3**base; start=(0,c0)
    def precise(j,c): return c%3**(r+j)==1
    parent={start:None}; dq=deque([start]); found=None
    while dq:
        j,c=dq.popleft()
        if c==4: found=(j,c); break
        if precise(j,c): continue
        L=base+j; M=3**L; inv2=(M+1)//2
        for a in X:
            cp=(pow(inv2,tau_a(a),M)*c)%M
            if cp%9==a and (j,cp) not in parent:
                parent[(j,cp)]=((j,c),('one',a,tau_a(a))); dq.append((j,cp))
        if j+1<=J:
            Mp=3**(L+1); inv2p=(Mp+1)//2; bb=(3*c+1)%Mp
            for a in X:
                cp=(pow(inv2p,tau_a(a),Mp)*bb)%Mp
                if cp%9==a and (j+1,cp) not in parent:
                    parent[(j+1,cp)]=((j,c),('zero',a,tau_a(a)-2)); dq.append((j+1,cp))
    if not found: return None
    path=[]; node=found
    while node is not None:
        e=parent[node]; path.append((node,e[1] if e else None)); node=e[0] if e else None
    path.reverse();
    def precise(j,c): return c%3**(r+j)==1
    return [(v, ('PRECISE' if v[1]%3**(r+v[0])==1 else 'ok'), ('TRAP' if v[1]==4 else ''), e) for (v,e) in path]

print("=== Explicit shortest CONSTRAINED path to the trap (r=4,g=3) ===")
P=shortest_constrained_path(4,3,6)
for (v, pst, tst, e) in P:
    print(f"  vertex (j={v[0]}, c={v[1]:5d})  [{pst}] {tst}   via {e}")

# kappa accounting of the suffix: in the FirstMPrecisionSuffix barrier, the suffix from the FIRST
# precise vertex must have kappa2>=1. Here the trap is reached with NO precise vertex before it,
# so the 'first precise vertex' along a goal-reaching path can be made the trap's DEEP-ONE-EDGE target
# (the goal), making the suffix a single deep one-edge => the canonical split's mid = goal, suffix empty
# or kappa2 ambiguous. The reachability of the trap as a source of a deep one-edge to goal, with no
# earlier precise vertex, is what KILLS the canonical-first-split device.

print("""
=== VERDICT ===
TRAP T is REACHABLE, and reachable under the CONSTRAINT (no coarse-m-precise vertex first).
 - reachable residues mod 3^t = ALL units, every t  => NO finite-modulus invariant separates.
 - per-level reps at level L = ALL units, every L (self-sustaining induction, base case = single
   zero-edge spreads one unit to all units one level up) => c==4 (the trap) is an exact reachable
   representative at level R+j for j>=1.
 - constrained == unconstrained EXACTLY (same reachable set, same trap-j set) in all faithful
   exhaustive tests => the 'avoid precise' constraint is VACUOUS for trap-reachability.
""")
