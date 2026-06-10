"""
Angle B3 -- the reachable dlog-residue SET mod 2*3^t (deterministic-digit automaton),
done correctly this time.

Two separate questions:
 (A) UNCONSTRAINED:  is residue 2 in the forward-reachable dlog set from d0 mod 2*3^t?
     If NO for some t -> the trap dlog=2 is UNREACHABLE at all (barrier holds, strongly).
 (B) The reachable set's structure: how large is it, what coset/subgroup.

We must use d0 mod 2*3^t with the TRUE d0 = dlog(aS202 mod 3^K) at a level K >= t+1,
NOT the small-level artifact.  Since aS202 == 1+3^22, d0 == 0 (mod 2*3^21) but NOT mod
2*3^22.  So for t<=21, d0 mod 2*3^t == 0; for t>=22 it is genuinely nonzero.

We compute reachable set for t up to ~14 (N=2*3^14 ~ 9.5M, borderline) using the
deterministic edges.  We DO include zero-edges (unbounded j hidden by truncation; valid
because determinacy holds for all levels).
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202
from b3_automaton_decide import build_J_table, automaton_edges
from collections import deque

def dlogv(c,k): return fast_dlog(c%3**k,k)

def reachable_set(t, d0, allow_zero=True, level=None, cap=20_000_000):
    Jtab,N=build_J_table(t, level=level)
    d0%=N
    seen=set([d0]); dq=deque([d0])
    while dq and len(seen)<cap:
        d=dq.popleft()
        for (kind,dp,om) in automaton_edges(d,N,Jtab,allow_zero=allow_zero):
            if dp not in seen:
                seen.add(dp); dq.append(dp)
    return seen,N

if __name__=="__main__":
    # true d0 at a big level so its low digits are correct
    K=80
    d0_true=dlogv(aS202()%3**K, K)
    print(f"true d0 = dlog(aS202) at level {K} = {d0_true}")
    print(f" d0 mod 2*3^t for t=18..24:")
    for t in range(18,25):
        print(f"   t={t}: d0 mod 2*3^{t} = {d0_true % (2*3**t)}  (==0? {d0_true%(2*3**t)==0})")
    print()
    print("=== (A) UNCONSTRAINED reachability of residue 2 (with zero-edges) ===")
    for t in range(1,13):
        S,N=reachable_set(t, d0_true, allow_zero=True)
        print(f" t={t} N={N:>8}: |reachable|={len(S):>8} (frac={len(S)/N:.4f})  2 in S? {2 in S}  0 in S? {0 in S}")
    print()
    print("=== one-edge-only reachable set (from a representative trap-adjacent? no: from d0) ===")
    for t in range(1,9):
        S,N=reachable_set(t, d0_true, allow_zero=False)
        print(f" t={t} N={N:>6}: |reach|={len(S)} S={sorted(S) if len(S)<=12 else '...'}  2 in S? {2 in S}")
