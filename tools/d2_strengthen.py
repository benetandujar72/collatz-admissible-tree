"""
ANGLE D2, part 4 (the charitable salvage): can a STRENGTHENED induction hypothesis
close the +1 gap?

Standard fix for a failing induction: strengthen the invariant.  The natural
strengthenings and why each fails:

S1. "kappa >= m for every path InvStart m -> v with v m-PRECISE (not just an m-goal)."
    - Is it TRUE?  An m-precise v has projpi(v) an m-goal.  By WPath_projectDown the
      path projects to InvStart m -> projpi(v) = m-goal, and hBar(m) gives kappa>=m.
      So S1 is EQUIVALENT to hBar(m) (no new content) -- it is literally hBar(m)
      applied through projpi.  It does NOT bound paths to NON-m-precise v.
    - Does it close the gap?  NO.  To bound the prefix InvStart(m+1)->mid we still
      need mid m-precise.  Same wall.

S2. "kappa >= m for EVERY path InvStart m -> v (any v)."  -- FALSE.
    - The empty path InvStart m -> InvStart m has kappa = 0 < m (for m>=1).
    - More generally any short prefix has small kappa.  A prefix barrier to an
      arbitrary vertex is FALSE, so it cannot be an invariant.

S3. "kappa + (precision deficit budget) >= m+1" -- a POTENTIAL-style invariant.
    - This is exactly S202_kappa_precise_barrier_bounded_from_potential: a potential
      Phi with Phi(InvStart) >= m+1, Phi(goal) <= 0, edge-monotone (Phi(v) <= kappa+Phi(v')).
    - This is the REAL target and is NOT inductive-in-m at all; it is the analytic
      barrier whose existence is the open problem.  Building such Phi uniformly in m
      is precisely Wall-A / the discrete-log (Baker) obstruction.  It does NOT reduce
      to hBar(m); it SUPERSEDES the induction.

S4. "strong induction: kappa >= k for paths in the k-cylinder, all k<=m, simultaneously."
    - Each k-instance is still a barrier to a k-GOAL.  Combining them does not bound a
      prefix to a non-goal.  No new lever.  Same wall as S1.

S5. "kappa1 >= m via a DIFFERENT cut than the first m-precise vertex."
    - Any cut whose prefix we bound by hBar(m) must project to an m-goal == be
      m-precise.  The set of IH-bindable cuts = {m-precise vertices on the path}.
    - On the trap witness that set = {goal} (shield).  The goal-cut has empty suffix
      (kappa2=0).  So NO cut in the IH-bindable set yields kappa2>=1.  Independent of
      WHICH m-precise cut: there is only one, and it is terminal.

CONCLUSION OF THE SALVAGE SURVEY:
  Every strengthening that stays INDUCTIVE-IN-m (S1, S4, S5) reduces to hBar(m) on a
  projected goal-path and bounds only the TOTAL or m-precise-prefixes -> deficit +1.
  Every strengthening that could close the gap (S3, the potential) is NOT inductive-in-m
  -- it is the analytic/Baker barrier itself, which is the open problem the induction
  was meant to AVOID.  S2 is outright false.

  => The uniform-in-m kappa-route is INADEQUATE.  The +1 cannot be produced by the
  induction; it requires either (i) an m-precise interior cut (REFUTED by the trap
  witness for the uniform statement), or (ii) a genuine 3-adic potential / discrete-log
  bound (Wall-A / Baker), which is not an induction at all.
"""

print(__doc__)

# Sanity: confirm S1 is non-vacuous-equivalent to hBar(m) and S2 is false at the start.
m = 1
# S2 counterexample: empty path kappa=0 at InvStart m, which is m-precise? NO:
# invStart_succ_not_mPrecise shows InvStart(m+1) is NOT m-precise; and InvStart m is
# itself not an m-goal (aS202 != 1 mod 3^(22m+2)).  So InvStart m is a NON-goal with
# kappa=0 reachable trivially => any "all-paths" prefix barrier is false.
print(f"S2 check: empty path at InvStart {m} has kappa=0 < m={m}; InvStart {m} is a")
print(f"          NON-goal (aS202 = 1+3^22 != 1 mod 3^(22*{m}+2)).  => S2 FALSE.\n")

print("FINAL VERDICT: salvage of the uniform-in-m kappa-route via a strengthened,")
print("still-inductive IH is IMPOSSIBLE.  The only gap-closing invariant is the analytic")
print("potential (Wall-A / Baker discrete-log), which is not the induction.  ANGLE D2's")
print("decoupling target -- kappa1>=m without m-precision -- has no lever and is refuted")
print("on the trap witness.")
