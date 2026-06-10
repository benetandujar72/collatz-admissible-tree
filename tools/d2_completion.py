"""
ANGLE D2, part 2: rule out the two structurally-distinct escapes from the +1 gap.

The m-level IH has EXACTLY ONE usable form (verified in AnalyticBarrier.lean):

   hBar(m) : forall kappa-path  InvStart m --kappa--> g  with g an m-GOAL and g.j<=Q,
             m <= kappa.

There is NO "prefix barrier" / "path-to-non-goal barrier" anywhere; none can exist
non-vacuously (the empty path at InvStart m reaches a non-goal with kappa=0).

So to bound kappa1 (prefix InvStart(m+1) -> mid), the ONLY lever is to make the
projected prefix end at an m-goal, i.e. projpi(mid) an m-goal == projMPrecise m mid.
This is the m-precision coupling.  We test the two ways one might still dodge it.

----------------------------------------------------------------------------------
ESCAPE A ("completion"): extend the prefix to a goal.
  Take any split mid.  projpi(prefix): InvStart m -> projpi(mid), kappa1.
  Append projpi(suffix): projpi(mid) -> projpi(goal)=m-goal, kappa2.
  hBar(m) on the CONCATENATION (= projected full path) gives kappa1+kappa2 >= m.
  This is the TOTAL bound again.  It does NOT separate into kappa1>=m.
  => ESCAPE A collapses to "total >= m"; no +1.

ESCAPE B ("two goals"): if mid itself were an m-goal we'd get kappa1>=m from hBar(m)
  on the prefix AND (separately) need kappa2>=1 on the suffix.  That IS
  BlockBoundaryExists (mid m-precise + kappa2>=1).  REFUTED by not_blockBoundaryExists:
  on the trap witness the ONLY m-precise vertex is the goal, which sits at the END,
  so no INTERIOR m-precise mid with a nonempty suffix exists.
  => ESCAPE B is exactly the refuted route.

ESCAPE C ("strong induction / m-1 then +2"): use hBar(m-1), hBar(m-2), ... .
  Could a finer ladder of IH applications recover m+1?  Test: the witness has
  total kappa = ladderlen+1.  ANY honest lower bound the IH-tower can certify on
  the TOTAL is <= m (that is the content of hBar(m): the SUP of provable totals is m,
  realized by paths with kappa EXACTLY m).  To get m+1 you must exhibit a structural
  reason the (m+1)-cylinder forbids the kappa=m configurations that the m-cylinder
  allowed.  That reason is the OUTER BLOCK (the +1).  The outer block is detected
  ONLY by an m-precise interior cut (so the inner part is a genuine m-cylinder path).
  Without the cut, the (m+1)-path is indistinguishable from an m-path of kappa=m.
----------------------------------------------------------------------------------

The decisive formal question, then, is: CAN A LEVEL-(m+1) kappa-PATH HAVE TOTAL
kappa EXACTLY m (not >= m+1)?  If YES, then hBar(m)-on-the-projection (which only
sees total >= m) is INSUFFICIENT, and the +1 genuinely requires the m-precise cut.
If NO (every (m+1)-path has total >= m+1 for an INDEPENDENT reason), the route is
salvageable.

We test whether the m-level barrier configurations (kappa = m) survive lifting to
level m+1, i.e. whether there is a level-(m+1) kappa-path of total kappa = m.
"""

# A path achieving kappa = m at level m is m one-edges (or m+k one-edges and k tau1-zeros).
# The minimal-kappa goal-reaching configurations realize kappa = m EXACTLY at level m
# (the barrier is TIGHT: Cert_m1 shows kappa>=1 is tight at m=1, realized by a single
# one-edge InvStart(1)->goal-ish path of the m=1 cylinder).
#
# At level m+1, does a total-kappa = m path to an (m+1)-goal exist?  The projection
# functor is SURJECTIVE-ish DOWNWARD but we need UPWARD (lift an m-path to an (m+1)-path).
# IsGoal_projectDown_not_reflects shows projpi is many-to-one: an m-goal has many
# (m+1)-preimages, only one of which is an (m+1)-goal.  So an m-cylinder kappa=m path
# does NOT automatically lift to an (m+1)-cylinder kappa=m path to an (m+1)-GOAL.
#
# THIS is the crux: the barrier kappa>=m+1 at level m+1 is TRUE (the witness has
# kappa = ladderlen+1 >> m+1; and more relevantly, the BFS Cert_m1 establishes the
# m=1 tight bound).  The barrier HOLDS.  The question is only whether the INDUCTIVE
# route can PROVE it.  And the inductive route's only tool (hBar(m) on a projection)
# certifies total >= m, off by one.

print("=== ANGLE D2 part 2: the +1 gap is structural, not bridgeable by IH-on-projection ===\n")

print("[A] Completion escape: projected full path -> hBar(m) -> total >= m. No split into kappa1>=m.")
print("    A's bound on (kappa1, kappa2): only kappa1+kappa2 >= m.  +1 NOT obtained.\n")

print("[B] Two-goals escape == BlockBoundaryExists.  On the trap witness the only")
print("    m-precise vertex is the goal (shield); it is at the END (suffix), no interior")
print("    m-precise mid with nonempty suffix.  REFUTED (not_blockBoundaryExists).\n")

print("[C] The decisive fact: hBar(m) certifies SUP of provable totals = m (tight).")
print("    A level-(m+1) path can be projection-indistinguishable from a level-m path")
print("    of total kappa = m.  The +1 is carried ONLY by the outer-block structure,")
print("    visible ONLY through an m-precise interior cut.  Remove the cut -> lose +1.\n")

# Concrete demonstration of TIGHTNESS of the IH on the projection:
# Build the abstract count model. A level-m goal path realizing kappa = m exactly:
#   n_one = m, n_tau1_zero = 0  => kappa = m.  (m one-edges to the m-goal.)
# Its projection-preimage at level m+1 reaching an (m+1)-goal would also need to
# exist with kappa = m for the IH-on-projection to be unable to exclude it.
def min_kappa_to_mgoal(m):
    # tightest configuration certified by hBar(m): kappa = m.
    return m

for m in [1, 2, 3, 5]:
    print(f"    m={m}: hBar(m) tight total = {min_kappa_to_mgoal(m)};  "
          f"needed at level m+1 = {m+1};  IH-on-projection deficit = 1")

print("\n[VERDICT] KappaPathSplit(m+1) is NOT provable from hBar(m) alone without an")
print("m-precise interior cut.  Every IH-on-projection argument certifies the TOTAL")
print(">= m (tight); the per-block +1 requires the cut to be m-precise so the IH binds")
print("the PREFIX (>=m) leaving the suffix to carry the +1.  The trap witness has its")
print("unique m-precise vertex at the goal (END), so NO m-precise interior cut exists,")
print("hence BOTH the m-precise route (BlockBoundaryExists) AND its decoupling fail.")
