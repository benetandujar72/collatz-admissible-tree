/-
**Crystallised reduction of the uniform-in-m slope barrier — corrected.**

Building on `KappaSplitWork.lean` (the proven R2 precision-reduction functor
`projπ` / `WPath_projectDown` / `kappaProjectsDown_holds`), this module reduces
the open core `KappaPathSplit` — and the whole uniform-in-m slope barrier — to a
SINGLE named open hypothesis, with the R2 functor and the induction discharged.

**Why a single hypothesis, not two (the R1 finding).** One is tempted to split
`KappaPathSplit` into (R2-prefix) + (R1-suffix), with R1 the standalone claim
"`OuterBlockIncrement`: any suffix from a block boundary forces `κ₂ ≥ 1`". This is
FALSE: `outerBlockIncrement_false` below refutes it (the *empty* suffix at any
goal is a counterexample, since an `(m+1)`-goal `projπ`-projects to an `m`-goal).
So the per-block increment `κ₂ ≥ 1` cannot be peeled off as a universal lemma —
it is intrinsically coupled to the choice of a *non-trivial* split point, hence
folded into the single crux:

  * `BlockBoundaryExists m Q` — every level-`(m+1)` κ-path admits a distinguished
    `mid` whose prefix `projπ`-projects onto an `m`-goal AND whose suffix has
    `κ₂ ≥ 1` (a genuine outer block). The non-constructible core (cf.
    `kappa_no_canonical_depth_cut`, `IsGoal_projectDown_not_reflects`).

`kappaPathSplit_of_block` proves: the m-level barrier (induction hypothesis) +
`BlockBoundaryExists` ⟹ `KappaPathSplit m Q`. The prefix bound `m ≤ κ₁` comes
from applying the IH barrier to the projected prefix.

HONEST SCOPE: CLOSES nothing new — records, in verified Lean, the precise open
content (a single satisfiable `Prop`, never an axiom) and the R1 impossibility.
NOT the `S202_alternative_conjecture`, NOT Collatz. 0 sorry. CAVEAT C inherited
(`InvStart` is the wrong cylinder for `m ≥ 2` until migrated to `aS202_at m`).
-/

import CollatzLean4.KappaSplitWork

namespace CollatzLean4.Admissible

/-- **R1 as a standalone universal (FALSE — see `outerBlockIncrement_false`).**
The naive "outer block forces `κ₂ ≥ 1`" quantified over all `(mid, suffix)` with
`projπ mid` an `m`-goal. Kept only to record its refutation. -/
def OuterBlockIncrement (m Q : Nat) : Prop :=
  ∀ {mid goal : InvVertex} {κ₂ : Int} {vs₂ : List InvVertex},
    InvVertex.IsGoal goal (22 * (m + 1) + 2) → goal.j ≤ Q →
    InvVertex.IsGoal (projπ m mid) (22 * m + 2) →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) mid goal κ₂ vs₂ →
    (1 : Int) ≤ κ₂

/-- **R1 cannot be a standalone lemma.** `OuterBlockIncrement` is refutable: take
`mid = goal = ⟨0, 1⟩` (the root vertex, a goal at every precision) with the empty
suffix, so `κ₂ = 0`; every hypothesis holds (an `(m+1)`-goal `projπ`-projects to
an `m`-goal) yet `1 ≤ 0` fails. Hence the per-block increment must be coupled to a
*non-trivial* split point, folded into `BlockBoundaryExists`. -/
theorem outerBlockIncrement_false (m Q : Nat) : ¬ OuterBlockIncrement m Q := by
  intro h
  have hg : InvVertex.IsGoal (⟨0, 1⟩ : InvVertex) (22 * (m + 1) + 2) := by
    show (1 : Nat) % 3 ^ (22 * (m + 1) + 2 + 0) = 1 % 3 ^ (22 * (m + 1) + 2 + 0)
    rfl
  have hpg : InvVertex.IsGoal (projπ m (⟨0, 1⟩ : InvVertex)) (22 * m + 2) := by
    show (1 % 3 ^ (22 * m + 2 + 0)) % 3 ^ (22 * m + 2 + 0) = 1 % 3 ^ (22 * m + 2 + 0)
    exact Nat.mod_mod _ _
  have hpath :
      WPath (InvKappaPreciseEdge (22 * (m + 1) + 2))
        (⟨0, 1⟩ : InvVertex) (⟨0, 1⟩ : InvVertex) 0 [] := ⟨rfl, rfl⟩
  have hjQ : (⟨0, 1⟩ : InvVertex).j ≤ Q := Nat.zero_le Q
  have hcontra : (1 : Int) ≤ 0 := h hg hjQ hpg hpath
  norm_num at hcontra

/-- **The split crux (open, single hypothesis).** Every level-`(m+1)` κ-path from
`InvStart (m+1)` to a goal of depth `≤ Q` admits a distinguished `mid` whose
prefix `projπ`-projects onto an `m`-goal, whose suffix has `κ₂ ≥ 1`, and with the
path data concatenating. The genuine non-constructible core. A `Prop`, never an
axiom. -/
def BlockBoundaryExists (m Q : Nat) : Prop :=
  ∀ {goal : InvVertex} {κ : Int} {vs : List InvVertex},
    InvVertex.IsGoal goal (22 * (m + 1) + 2) → goal.j ≤ Q →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) goal κ vs →
    ∃ (mid : InvVertex) (κ₁ κ₂ : Int) (vs₁ vs₂ : List InvVertex),
      WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) mid κ₁ vs₁ ∧
      WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) mid goal κ₂ vs₂ ∧
      κ = κ₁ + κ₂ ∧ vs = vs₁ ++ vs₂ ∧
      InvVertex.IsGoal (projπ m mid) (22 * m + 2) ∧ mid.j ≤ Q ∧ (1 : Int) ≤ κ₂

/-- **The reduction.** The m-level barrier (induction hypothesis) together with
the single crux `BlockBoundaryExists` yields `KappaPathSplit m Q`. The
precision-reduction step (R2) is discharged via `WPath_projectDown` +
`projπ_InvStart`; the prefix bound `m ≤ κ₁` comes from applying the m-level
barrier to the projected prefix; the suffix bound `1 ≤ κ₂` is supplied by the
crux. -/
theorem kappaPathSplit_of_block
    {m Q : Nat} (hm : 1 ≤ m)
    (hBar : S202_kappa_precise_barrier_bounded m Q)
    (hBlock : BlockBoundaryExists m Q) :
    KappaPathSplit m Q := by
  intro goal κ vs h_g h_goal_j h_path
  obtain ⟨mid, κ₁, κ₂, vs₁, vs₂, h_pre, h_suf, h_sum, h_vs, h_mid_goal, h_mid_j, h_κ₂⟩ :=
    hBlock h_g h_goal_j h_path
  have h_proj :
      WPath (InvKappaPreciseEdge (22 * m + 2)) (InvStart m) (projπ m mid) κ₁
        (vs₁.map (projπ m)) := by
    have h := WPath_projectDown h_pre
    rwa [projπ_InvStart m hm] at h
  have h_mid_j' : (projπ m mid).j ≤ Q := by rw [projπ_j]; exact h_mid_j
  have h_κ₁ : (m : Int) ≤ κ₁ := hBar h_mid_goal h_mid_j' h_proj
  exact ⟨mid, κ₁, κ₂, vs₁, vs₂, h_pre, h_suf, h_sum, h_vs, h_κ₁, h_κ₂⟩

/-- **Uniform κ-barrier from the single crux.** A base κ-barrier plus
`BlockBoundaryExists` at every level `≥ m₀` gives the κ-precise bounded barrier at
every level. Induction over `kappaPathSplit_of_block` + `barrier_step_of_split`. -/
theorem uniform_kappa_barrier_of_block
    {Q m₀ : Nat} (hm₀ : 1 ≤ m₀)
    (h_base : S202_kappa_precise_barrier_bounded m₀ Q)
    (h_block : ∀ m, m₀ ≤ m → BlockBoundaryExists m Q) :
    ∀ m, m₀ ≤ m → S202_kappa_precise_barrier_bounded m Q := by
  refine Nat.le_induction h_base ?_
  intro k hk ih
  have hk1 : 1 ≤ k := le_trans hm₀ hk
  apply barrier_step_of_split
  exact kappaPathSplit_of_block hk1 ih (h_block k hk)

/-- **End-to-end (conditional) uniform slope barrier.** A base κ-barrier plus the
single crux `BlockBoundaryExists` at every level yields the S202 slope barrier
`defect ≥ m` for every `m ≥ m₀`, via the committed non-circular chain. The entire
open content of the uniform-in-m slope-barrier route is therefore EXACTLY
`BlockBoundaryExists` (uniformly in `m`). -/
theorem uniform_slope_barrier_of_block
    {Q m₀ : Nat} (hm₀ : 1 ≤ m₀)
    (h_base : S202_kappa_precise_barrier_bounded m₀ Q)
    (h_block : ∀ m, m₀ ≤ m → BlockBoundaryExists m Q) :
    ∀ m, m₀ ≤ m → S216BarrierForWords m Q (m : Int) := by
  intro m hm
  exact S202_slope_barrier_from_actual_edge_count_bounded
    (S202_actual_edge_count_bounded_of_kappa_precise_barrier_bounded
      (uniform_kappa_barrier_of_block hm₀ h_base h_block m hm))

end CollatzLean4.Admissible
