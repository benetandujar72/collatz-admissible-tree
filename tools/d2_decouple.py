"""
ANGLE D2: Can KappaPathSplit (m+1) be proven from hBar(m) WITHOUT routing
through an m-precise BlockBoundaryExists?

The proposed escape: project the FULL (m+1)-path down to level m. By
WPath_projectDown the projected path is a genuine level-m kappa-path from
projpi(InvStart(m+1)) = InvStart m to projpi(goal), an m-goal (IsGoal_projectDown),
of the SAME total kappa. Apply hBar(m): kappa >= m.

PROBLEM: this gives kappa >= m for the WHOLE path, i.e. kappa1 + kappa2 >= m
where the split is anywhere. But KappaPathSplit needs kappa = kappa1 + kappa2 with
kappa1 >= m AND kappa2 >= 1, hence total >= m+1.

The question of D2: is there an ALTERNATIVE bound on kappa1 (the prefix) that
yields kappa1 >= m without m-precision of mid, OR a way to get total >= m+1
directly?

This script crystallizes the arithmetic obstruction on the ACTUAL trap witness
(LadderExists.lean) and tests every candidate decoupling.
"""

# -----------------------------------------------------------------------------
# The kappa weights (InvKappaPreciseEdge):
#   one-edge:            kappa = +1
#   tau=1 zero-edge:     kappa = -1
#   tau>=2 zero-edge:    kappa =  0
# Total kappa along a path = (#one-edges) - (#tau1-zero-edges).
# -----------------------------------------------------------------------------

# The witness path (InvStart(m+1) -> goal), from not_blockBoundaryExists:
#   InvStart(m+1)  --entry zero-edge (tau=4, kappa=0)-->  s1=<1,c1> (class 7)
#   s1  --one-edge ladder (each kappa=+1)-->  trap=<1,4> (class 4)
#   trap  --deep one-edge (tau=2, kappa=+1)-->  goal=<1,1>
#
# So: #one-edges = ladderlen + 1 (deep edge); #tau1-zeros = 0; #tau>=2 zeros = 1 (entry).
# Total kappa = ladderlen + 1.
#
# ladderlen ~ (W-2)/3 where W = dlog(c1) ~ 3^21 magnitude.  So total kappa is
# astronomically >> m+1.  The barrier kappa >= m+1 HOLDS for this witness.

def witness_kappa(ladderlen):
    n_one = ladderlen + 1   # ladder one-edges + deep one-edge
    n_tau1_zero = 0         # entry is tau=4 (kappa=0), not tau=1
    return n_one - n_tau1_zero

# -----------------------------------------------------------------------------
# KEY STRUCTURAL FACT to verify: the projection of the FULL witness path.
#
# projpi m <j,c> = <j, c % 3^(22m+2+j)>.  kappa is PRESERVED edgewise
# (InvKappaPreciseEdge_projectDown).  So the projected path has the SAME total
# kappa = ladderlen+1 >= m+1.  Applying hBar(m) to it gives only kappa >= m,
# which is WEAKER than what the projected path already has.  The IH is SLACK on
# the projection: projection -> kappa >= m, but the real kappa is ladderlen+1.
#
# The +1 we need is NOT recoverable from "kappa(projected) >= m" because that is
# the bound on the TOTAL, and the total IS >= m, but we want the SPLIT to give
# m on the prefix and 1 on the suffix.
# -----------------------------------------------------------------------------

# Now: WHERE on the projected path is the projected goal a goal, and does the
# m-level IH see "the first m-goal" anywhere BEFORE the end?
#
# Under projpi m, a vertex <1,c> with c = 2^d % 3^(R+1) (R=22(m+1)+2) projects to
#   <1, (2^d % 3^(R+1)) % 3^(22m+2+1)> = <1, 2^d % 3^(22m+3)>   (since 22m+3 <= R+1)
# i.e. the SAME ladder, one precision level down.  Is any ladder vertex an
# m-goal after projection?  m-goal at j=1 means c_proj ≡ 1 (mod 3^(22m+3)).
# Ladder vertices have c_proj = 2^d % 3^(22m+3) with class 4 or 7 mod 9, so
# c_proj mod 9 in {4,7} != 1.  Hence NO projected ladder vertex is an m-goal.
# The projected goal <1,1> is the unique m-precise vertex on the projected path
# too.  So projecting does NOT create an earlier m-goal to split at.

def class_mod9_of_ladder(d):
    # 2^d mod 9 has period 6; ladder uses d ≡ 2 (class 4) or d ≡ 4 (class 7) mod 6.
    return pow(2, d, 9)

def is_mgoal_projected_ladder_vertex(d, m):
    # projected ladder vertex <1, 2^d % 3^(22m+3)>; m-goal iff ≡ 1 mod 3^(22m+3).
    # Equivalent (necessary) mod 9: 2^d % 9 == 1 % 9 == 1.
    return pow(2, d, 9) == 1

# Verify the shield survives projection: no ladder d in {2,4 mod 6} gives class 1.
def verify_shield_under_projection():
    bad = []
    for d in range(2, 200):
        if d % 6 in (2, 4):
            if is_mgoal_projected_ladder_vertex(d, m=1):
                bad.append(d)
    return bad  # expect empty

print("=== ANGLE D2: decoupling kappa1 >= m from m-precision ===\n")

print("[1] Witness total kappa vs needed bound:")
for ladderlen in [1, 5, 100]:
    for m in [1, 3]:
        tk = witness_kappa(ladderlen)
        print(f"    ladderlen={ladderlen:4d} m={m}: total kappa={tk:4d}  "
              f">= m+1={m+1}? {tk >= m+1}   (IH on projection only gives >= m={m})")

print("\n[2] Shield survives projection (no projected ladder vertex is an m-goal):")
bad = verify_shield_under_projection()
print(f"    ladder vertices d in [2,200) with d%6 in {{2,4}} that are projected m-goals: {bad}")
print(f"    => shield holds under projection: {bad == []}")

# -----------------------------------------------------------------------------
# [3] The CRUX of D2.  Suppose we DON'T demand mid m-precise.  KappaPathSplit
# only needs SOME split mid with kappa1 >= m and kappa2 >= 1.  Candidate bounds
# on kappa1 that avoid m-precision:
#
#   (a) Apply hBar(m) to the projected PREFIX InvStart(m+1)->mid.
#       projpi(prefix) is a kappa-path InvStart m -> projpi(mid).  hBar(m)
#       REQUIRES projpi(mid) to be an m-GOAL.  That IS m-precision of mid.
#       => (a) cannot avoid m-precision; it is exactly the blocked route.
#
#   (b) Apply hBar(m) to the projected FULL path (prefix++suffix):
#       gives kappa1+kappa2 >= m, i.e. total >= m.  Then pick the LAST edge as
#       the suffix (kappa2 = its weight).  To get kappa2 >= 1 the last edge must
#       be a one-edge; on the witness it is (deep one-edge).  Then
#       kappa1 = total - kappa2 = total - 1 >= m - 1, NOT >= m.  Off by one.
#       => (b) yields kappa1 >= m-1, kappa2 >= 1 => total >= m, the IH bound.
#          It CANNOT manufacture the +1.
#
#   (c) Apply hBar(m) to the FULL path AND separately argue kappa2 >= 1 on a
#       nontrivial suffix.  Then total >= m gives kappa1 = total - kappa2.
#       If kappa2 >= 1 and total >= m, kappa1 >= m - kappa2 could be < m.
#       To force kappa1 >= m we'd need total >= m + kappa2 >= m+1.  But hBar(m)
#       only certifies total >= m.  CIRCULAR: getting total >= m+1 IS the goal.
# -----------------------------------------------------------------------------

print("\n[3] Candidate (b): split off the last one-edge as suffix.")
for ladderlen in [1, 5, 100]:
    for m in [1, 3]:
        total = witness_kappa(ladderlen)
        kappa2 = 1            # last (deep) one-edge
        kappa1 = total - kappa2
        ih_bound_on_total = m  # hBar(m) on projected full path
        # The honest bound we can PROVE for kappa1 via the projected full path:
        # kappa1 = total - kappa2; but we only KNOW total >= m, so kappa1 >= m - kappa2 = m-1.
        provable_kappa1_lb = ih_bound_on_total - kappa2
        print(f"    ladderlen={ladderlen:4d} m={m}: provable kappa1 >= {provable_kappa1_lb} "
              f"(need >= {m}); gap = {m - provable_kappa1_lb}")

print("\n[4] VERDICT arithmetic: hBar(m) on the projection certifies the TOTAL >= m.")
print("    KappaPathSplit needs total = kappa1+kappa2 with kappa1>=m, kappa2>=1, i.e. total>=m+1.")
print("    The IH gives total>=m, never total>=m+1.  The missing +1 is EXACTLY the")
print("    per-block increment that the m-precise prefix-projection was supposed to")
print("    supply (m on the prefix) ON TOP OF the suffix's +1.  Decoupling from")
print("    m-precision collapses prefix bound from >=m to >=m-1: the route loses the +1.")
