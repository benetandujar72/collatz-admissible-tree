/-
**Crystallised reduction of the uniform-in-m slope barrier.**

Building on `KappaSplitWork.lean` (the proven R2 precision-reduction functor
`projπ` / `WPath_projectDown` / `kappaProjectsDown_holds`), this module reduces
the open core `KappaPathSplit` — and hence the whole uniform-in-m slope barrier —
to EXACTLY TWO named open hypotheses, with everything else discharged:

  * `BlockBoundaryExists m Q` — the SPLIT crux: every qualifying κ-path to level
    `m+1` admits a distinguished `mid` whose prefix `projπ`-projects onto an
    `m`-level goal, with the path data concatenating. This is the genuine
    non-constructible obstruction (cf. `kappa_no_canonical_depth_cut` and
    `IsGoal_projectDown_not_reflects`: `projπ` is many-to-one, so `mid` cannot be
    recovered from the projection alone).
  * `OuterBlockIncrement m Q` — R1: the outermost `wS202`-block suffix forces at
    least one net one-edge, `κ₂ ≥ 1`. Gated on the path↔word bridge (S212.2) and
    the S213 context-uniformity frontier.

`kappaPathSplit_of_block_and_increment` proves: the m-level barrier (the induction
hypothesis) + these two ⟹ `KappaPathSplit m Q`. The precision-tower obligation is
discharged internally via `WPath_projectDown` + `projπ_InvStart`. The capstone
`uniform_slope_barrier_of_block_and_increment` then threads this through the
committed induction + non-circular chain to give `S216BarrierForWords m Q m` for
ALL `m ≥ m₀` from a base κ-certificate.

HONEST SCOPE: this CLOSES nothing new — it records, in verified Lean, the precise
open content of the route. Both `Prop`s are hypotheses, never axioms. The
`BlockBoundaryExists` crux remains the real wall; beyond the slope barrier lie the
formal `S202_alternative_conjecture` (different statement) and the external
Bandújar reduction to Collatz. NOT a Collatz proof. 0 sorry.

CAVEAT C (inherited, flagged): for `m ≥ 2` the start `InvStart m = ⟨0, aS202⟩`
uses the low-precision constant `aS202 = 1+3^22`, the WRONG S202 cylinder
(`aS202_at_2_ne_aS202_mod_3_46`); the m-level barrier hypothesis is only
meaningful once `InvStart` migrates to the coherent tower `aS202_at m`. The
reduction below is true as a statement about the graph objects regardless.
-/

import CollatzLean4.KappaSplitWork

namespace CollatzLean4.Admissible

/-- **R1 (open).** The outermost `wS202` block of a level-`(m+1)` κ-path forces
the suffix κ-cost `κ₂ ≥ 1` (at least one net one-edge), once the prefix is a true
block boundary (its `projπ`-image is an `m`-level goal). A `Prop`, never an
axiom. -/
def OuterBlockIncrement (m Q : Nat) : Prop :=
  ∀ {mid goal : InvVertex} {κ₂ : Int} {vs₂ : List InvVertex},
    InvVertex.IsGoal goal (22 * (m + 1) + 2) → goal.j ≤ Q →
    InvVertex.IsGoal (projπ m mid) (22 * m + 2) →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) mid goal κ₂ vs₂ →
    (1 : Int) ≤ κ₂

/-- **The split crux (open).** Every level-`(m+1)` κ-path from `InvStart (m+1)` to
a goal of depth `≤ Q` admits a distinguished `mid` such that the prefix
`InvStart (m+1) ⟶ mid` `projπ`-projects onto an `m`-level goal, with the κ-cost
and vertex list concatenating. This is the genuine non-constructible core. -/
def BlockBoundaryExists (m Q : Nat) : Prop :=
  ∀ {goal : InvVertex} {κ : Int} {vs : List InvVertex},
    InvVertex.IsGoal goal (22 * (m + 1) + 2) → goal.j ≤ Q →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) goal κ vs →
    ∃ (mid : InvVertex) (κ₁ κ₂ : Int) (vs₁ vs₂ : List InvVertex),
      WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) mid κ₁ vs₁ ∧
      WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) mid goal κ₂ vs₂ ∧
      κ = κ₁ + κ₂ ∧ vs = vs₁ ++ vs₂ ∧
      InvVertex.IsGoal (projπ m mid) (22 * m + 2) ∧ mid.j ≤ Q

/-- **The reduction.** The m-level barrier (induction hypothesis) together with the
two open hypotheses `BlockBoundaryExists` and `OuterBlockIncrement` yields
`KappaPathSplit m Q`. The precision-reduction step (R2) is discharged here via the
proven functor `WPath_projectDown` + `projπ_InvStart`; the prefix bound `m ≤ κ₁`
comes from applying the m-level barrier to the projected prefix. -/
theorem kappaPathSplit_of_block_and_increment
    {m Q : Nat} (hm : 1 ≤ m)
    (hBar : S202_kappa_precise_barrier_bounded m Q)
    (hBlock : BlockBoundaryExists m Q)
    (hSuffix : OuterBlockIncrement m Q) :
    KappaPathSplit m Q := by
  intro goal κ vs h_g h_goal_j h_path
  obtain ⟨mid, κ₁, κ₂, vs₁, vs₂, h_pre, h_suf, h_sum, h_vs, h_mid_goal, h_mid_j⟩ :=
    hBlock h_g h_goal_j h_path
  -- R2: the prefix projects to a level-m κ-path InvStart m ⟶ projπ mid of the SAME κ₁.
  have h_proj :
      WPath (InvKappaPreciseEdge (22 * m + 2)) (InvStart m) (projπ m mid) κ₁
        (vs₁.map (projπ m)) := by
    have h := WPath_projectDown h_pre
    rwa [projπ_InvStart m hm] at h
  have h_mid_j' : (projπ m mid).j ≤ Q := by rw [projπ_j]; exact h_mid_j
  -- prefix bound from the m-level barrier; suffix bound from R1.
  have h_κ₁ : (m : Int) ≤ κ₁ := hBar h_mid_goal h_mid_j' h_proj
  have h_κ₂ : (1 : Int) ≤ κ₂ := hSuffix h_g h_goal_j h_mid_goal h_suf
  exact ⟨mid, κ₁, κ₂, vs₁, vs₂, h_pre, h_suf, h_sum, h_vs, h_κ₁, h_κ₂⟩

/-- **Uniform κ-barrier from the two open hypotheses.** A base κ-barrier plus
`BlockBoundaryExists` and `OuterBlockIncrement` at every level `≥ m₀` give the
κ-precise bounded barrier at every level. Pure induction over
`kappaPathSplit_of_block_and_increment` + the committed `barrier_step_of_split`. -/
theorem uniform_kappa_barrier_of_block_and_increment
    {Q m₀ : Nat} (hm₀ : 1 ≤ m₀)
    (h_base : S202_kappa_precise_barrier_bounded m₀ Q)
    (h_block : ∀ m, m₀ ≤ m → BlockBoundaryExists m Q)
    (h_incr : ∀ m, m₀ ≤ m → OuterBlockIncrement m Q) :
    ∀ m, m₀ ≤ m → S202_kappa_precise_barrier_bounded m Q := by
  refine Nat.le_induction h_base ?_
  intro k hk ih
  have hk1 : 1 ≤ k := le_trans hm₀ hk
  apply barrier_step_of_split
  exact kappaPathSplit_of_block_and_increment hk1 ih (h_block k hk) (h_incr k hk)

/-- **End-to-end (conditional) uniform slope barrier.** A base κ-barrier plus the
two open hypotheses at every level yield the S202 slope barrier `defect ≥ m` for
every `m ≥ m₀`, via the committed non-circular chain. The entire open content of
the uniform-in-m slope-barrier route is therefore EXACTLY
`{BlockBoundaryExists, OuterBlockIncrement}` (uniformly in `m`). -/
theorem uniform_slope_barrier_of_block_and_increment
    {Q m₀ : Nat} (hm₀ : 1 ≤ m₀)
    (h_base : S202_kappa_precise_barrier_bounded m₀ Q)
    (h_block : ∀ m, m₀ ≤ m → BlockBoundaryExists m Q)
    (h_incr : ∀ m, m₀ ≤ m → OuterBlockIncrement m Q) :
    ∀ m, m₀ ≤ m → S216BarrierForWords m Q (m : Int) := by
  intro m hm
  exact S202_slope_barrier_from_actual_edge_count_bounded
    (S202_actual_edge_count_bounded_of_kappa_precise_barrier_bounded
      (uniform_kappa_barrier_of_block_and_increment hm₀ h_base h_block h_incr m hm))

end CollatzLean4.Admissible
