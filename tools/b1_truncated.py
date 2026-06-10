"""
B1 -- THE RIGOROUS ROUTE: exact BFS on the truncated residue c mod 3^t.

CLAIM (to verify): for R+j >= t, the edge maps reduce CLEANLY mod 3^t:
  one-edge:  c' == inv2^tau * c           (mod 3^t),  where inv2=(3^t+1)/2,
             admissibility c'%9==alpha=tau-preimage uses only c' mod 9 (<=t for t>=2).
  zero-edge: c' == inv2^tau * (3c+1)       (mod 3^t).
Both depend ONLY on c mod 3^t (since invMod2(3^(R+j)) == inv2 mod 3^t when R+j>=t).

Therefore the projection pi_t : vertex -> (c mod 3^t) is a FACTOR of the dynamics for the
*one-edge* (j fixed) and for the zero-edge the (3c+1) is also local. So the set
   Reach_t := { c mod 3^t : reachable from start }
is computable EXACTLY by BFS on Z/3^t (a finite set of size <= 3^t), PROVIDED j stays >= 0 and
the level R+j >= t which always holds once R >= t (R=22M+2 >= 46 >> t for our t<=10).

If 4 (== trap residue mod 3^t) is NOT in Reach_t for some t, then the trap is UNREACHABLE
==> a genuine separating invariant "c mod 3^t in Reach_t" with start in it, trap not.
This is RIGOROUS (exhaustive over a finite quotient) and Lean-formalizable.

We compute Reach_t for t=1..10 and report whether 4 mod 3^t is reachable.
We treat the zero-edge as ALWAYS available (Q=infinity) -- the MOST permissive; if the trap is
unreachable even with unlimited zero-budget, it is unreachable for every Q.  This makes the
invariant Q-uniform.
"""
def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
aS202=1+3**22

def reach_mod(t, allow_zero=True):
    M=3**t
    inv2=(M+1)//2
    invpow={a: pow(inv2, tau(a), M) for a in X}
    start=aS202 % M
    seen={start}
    frontier=[start]
    edges_used=set()
    while frontier:
        nf=[]
        for c in frontier:
            # one-edges: c' = invpow[a]*c % M, keep if c'%9==a (admissible)
            for a in X:
                cp=(invpow[a]*c) % M
                if cp % 9 == a:
                    if cp not in seen:
                        seen.add(cp); nf.append(cp)
                    edges_used.add(('one',a))
            if allow_zero:
                base=(3*c+1) % M
                for a in X:
                    cp=(invpow[a]*base) % M
                    if cp % 9 == a:
                        if cp not in seen:
                            seen.add(cp); nf.append(cp)
                        edges_used.add(('zero',a))
        frontier=nf
    return seen, edges_used

print("=== Reach_t = reachable residues c mod 3^t from start=aS202, unlimited zero-budget ===")
print(f"{'t':>2} {'|Reach_t|':>10} {'3^t':>10} {'frac':>8}  trap(4) reachable?  goal(1) reachable?")
for t in range(1,11):
    seen,_=reach_mod(t)
    M=3**t
    trap = (4 % M) in seen
    goal = (1 % M) in seen
    print(f"{t:>2} {len(seen):>10} {M:>10} {len(seen)/M:>8.4f}  {str(trap):>16}  {str(goal):>16}")
