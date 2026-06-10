"""
B1 -- the STRUCTURAL analysis of the dlog invariant.

Setup (m generic, work at m=1 concretely; R=22m+2=24).
A vertex v=(j,c). Working level for the (m+1)-barrier is B = 22(m+1)+2+j = 22m+24+j.
But the EDGES live at level R+j = 22m+2+j (one-edge) or R+j+1 (zero-edge), with R=22m+2.

Wait -- careful. The barrier FirstMPrecisionSuffixPositive is for the (m+1)-cylinder.
So its InvStart is InvStart(m+1), its edges use R' = 22(m+1)+2 = 22m+24.
  start level (j=0): k = 22m+24.
  trap T: v.c == 4 mod 3^(R'+j) = 3^(22m+24+j).
  goal:   v.c == 1 mod 3^(22m+24+j).
  m-precise: v.c == 1 mod 3^(22m+2+j)   [the COARSER level, 22 digits below].

So set M := m+1 and work with the M-cylinder barrier. Let me rename: the barrier index is M=m+1>=2.
  Rbar = 22*M + 2.  start = aS202 % 3^Rbar.  edges at level Rbar+j.
  trap, goal at level Rbar+j.  m-precise (coarse) at level Rbar+j-22.

KEY dlog facts (cocycle, all at the SAME level k=Rbar+j for a one-edge):
  dlog_k(source) = tau(target) + dlog_k(target)  (mod 2*3^{k-1})    [oneEdge_dlog_shift]
So FORWARD along edges (start -> ... -> goal), the dlog telescopes:
  dlog_k(start_at_level_k)  vs  dlog along the path.
BUT the modulus level k CHANGES at zero-edges (k -> k+1). So the cocycle moduli differ.

The cleanest invariant lives at a FIXED low level. Reduce everything mod 3^t0 for small t0:
the projection ZMod 3^{k+1} -> ZMod 3^k is a ring hom fixing 2, so dlog_k(c) = dlog_{k+1}(c) mod 2*3^{k-1}
[dlog_reduce, VERIFIED]. So the dlog *mod 2*3^{t-1}* is well-defined independent of which finer level
we measure at, AS LONG AS the c-residue's low part is fixed.
"""

def tau(n):
    return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
aS202 = 1+3**22

import sys
sys.path.insert(0,".")
from b1_dlog_fast import dlog_fast

# ---------------------------------------------------------------
# Observation 1: dlog(aS202 mod 3^k) == 0 mod (2*3^21) for all k.
print("=== Obs 1: dlog(start) is divisible by 2*3^21 (the 'depth-21 seed') ===")
for k in [23,24,25,30,46,56]:
    a = aS202 % 3**k
    d = dlog_fast(k,a)
    base = 2*3**21
    print(f"  k={k}: dlog%(2*3^21) = {d % base}  (so d = {d//base} * 2*3^21)")

# This is just because aS202 = 1 + 3^22 == 1 (mod 3^22), so 2^d == 1 (mod 3^22),
# forcing d == 0 (mod ord_{3^22}(2)=2*3^21).  Let's CONFIRM the mechanism:
print("  mechanism: aS202 mod 3^22 =", aS202 % 3**22, "(==1), so dlog == 0 mod ord(2 mod 3^22)=2*3^21")

# ---------------------------------------------------------------
# The trap has dlog = 2 (a fixed SMALL number, NOT divisible by 2*3^21).
# Goal has dlog = 0.
# Question: does the edge cocycle preserve "dlog == 0 mod (small modulus)"?
#
# The per-edge shift is +tau(target) with tau in {1,2,3,4}. These are NOT multiples of
# anything nice. So dlog mod (2*3^21) is NOT preserved by a single edge -- it shifts by tau.
# Hence NO fixed-low-level dlog-residue invariant survives a single edge UNLESS tau is
# constrained. Let's see if there is a *combined* (dlog, something) monotone.
print("\n=== Obs 2: per-edge dlog shift is +tau, tau in {1,2,3,4}; not a fixed residue invariant ===")
print("  tau values over X:", {a:tau(a) for a in X})

# ---------------------------------------------------------------
# Reformulate via the SIGN bit (mod 2). dlog % 2 = [c%3==2]. VERIFIED closed form.
# start: aS202 % 3 = 1 -> sign 0. trap c==4 -> 4%3=1 -> sign 0. goal c==1 -> sign 0.
# So the SIGN bit does NOT separate start(0)/trap(0)/goal(0). Mod-2 is useless. Confirmed.
print("\n=== Obs 3: sign bit (dlog mod 2) ===")
print(f"  start: (aS202%3)={aS202%3} -> sign {1 if aS202%3==2 else 0}")
print(f"  trap c=4: 4%3={4%3} -> sign {1 if 4%3==2 else 0}")
print(f"  goal c=1: 1%3={1%3} -> sign {1 if 1%3==2 else 0}")
print("  => mod-2 does NOT separate. (matches mod-9 evidence: c==4 common)")

# ---------------------------------------------------------------
# The principal 3-adic part: dlog mod 3^t (the analytic part).
# start dlog == 0 mod 3^21. trap dlog=2: 2 mod 3^t = 2 for t>=1. goal 0.
# So at modulus 3^t (t<=21): start residue 0, trap residue 2, goal residue 0.
# The per-edge shift +tau moves this by tau mod 3^t. Over many edges, the reachable set of
# (dlog mod 3^t) is {0 + sum tau_i mod 3^t}. Since tau in {1,2,3,4} hits residues 1,2,0(=3),1(=4 mod3),
# the additive subgroup generated is ALL of Z/3^t. So mod-3^t alone: trap IS reachable additively.
print("\n=== Obs 4: reachable (dlog mod 3^t) under +tau steps ===")
for t in [1,2,3]:
    M=3**t
    reach=set([0])
    for _ in range(50):
        new=set()
        for d in reach:
            for a in X:
                new.add((d+tau(a))%M)
        if new<=reach: break
        reach|=new
    print(f"  t={t}: reachable dlog mod 3^{t} from 0 via +tau = {sorted(reach)} ; 2 in it? {2%M in reach}")
print("  => additively, +tau generates everything mod 3^t. NO additive obstruction.")
print("     The obstruction (if any) must couple tau to the REALIZABILITY of edges (consistency).")
