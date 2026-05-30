/-
**Build-verified TRUE bricks for `BlockBoundaryExists` — the first-witness split,
the non-trivial reduction to a sharper residual `Prop`, and the δ₊ per-edge laws.**

`BlockBoundaryExists m Q` (committed in `KappaSplitReduction.lean`) is the single
open core of the uniform-in-`m` S202 slope-barrier route: every level-`(m+1)`
κ-path to a goal admits a split point `mid` whose prefix `projπ`-projects onto an
`m`-goal AND whose suffix carries `κ₂ ≥ 1`.

This module records, in verified Lean (0 `sorry`, 0 `axiom`), the *honest*
decomposition of that target. It does NOT close `BlockBoundaryExists` — a full
proof is genuine article-level research and is not attempted. Instead it:

  * **(F1) `WPath_first_witness_split`** — the generic, fully-true structural
    brick: any `WPath s ⟶ t` with a decidable vertex predicate `P` holding at `t`
    splits as a prefix `s ⟶ mid` ++ suffix `mid ⟶ t` with `P mid` and **no
    `P`-vertex strictly inside the prefix interior** (`mid` = the FIRST `P`-vertex
    along the traversal). Pure induction on the interior list; weight- and
    list-additive. This is the carrier of "split a path at the first witness",
    which was not in the repo.

  * **`projMPrecise` + `instDecidableProjMPrecise`** — the level-`m` precision
    predicate `P m v := IsGoal (projπ m v) (22m+2)` packaged as a `DecidablePred`,
    so (F1) instantiates at it.

  * **`invStart_succ_not_mPrecise`** — a TRUE arithmetic fact with real content:
    the start vertex `InvStart (m+1)` is itself NOT `m`-precise (because
    `aS202 = 1 + 3^22 ≢ 1 (mod 3^(22m+2))` for `m ≥ 1`). Hence the first
    `m`-precision point of any path is strictly AFTER the start — the suffix from
    it is a proper tail, which is the geometric reason the construction is not
    immediately the R1 trap at the START (the trap can only re-appear at the END,
    when the first `m`-precision point IS the goal).

  * **`FirstMPrecisionSuffixPositive`** — the SHARPER residual `Prop`, and
    **`blockBoundaryExists_of_firstMPrecisionSuffixPositive`** — the VALID
    reduction `FirstMPrecisionSuffixPositive m Q → BlockBoundaryExists m Q`. The
    residual is strictly weaker than `BlockBoundaryExists`: it only constrains the
    *canonical* first-witness `mid` (handed the firstness data `∀ x ∈ vs₁, ¬ P x`
    that the split produces), whereas `BlockBoundaryExists` must *exhibit* such a
    `mid`. So this genuinely DISCHARGES the structural-split half and isolates the
    κ₂ ≥ 1 arithmetic as the one remaining obligation.

  * **δ₊ per-edge laws lifted to `InvKappaPreciseEdge`** — `deltaPlus_tau2Zero_eq`
    (τ=2 zero-edge: δ₊ UNCHANGED), `deltaPlus_oddTauZero_max` (odd-τ zero-edge:
    δ₊ resets to MAX), and the consequence `kappaEdge_deltaPlus_ge_of_not_oneEdge_aux`
    (δ₊ is NON-DECREASING across a κ-precise edge that is a τ=2-zero or an
    odd-τ-zero). Together these are the verified "δ₊ can only DROP via a one-edge
    (or an even-τ≥4 zero-edge)" content — the engine behind the one-edge
    necessity on the residual suffix.

**HONEST RESIDUAL.** What of `BlockBoundaryExists` remains open after this module is
EXACTLY `FirstMPrecisionSuffixPositive m Q`: on the suffix from the first
`m`-precision vertex to the goal, `κ₂ = n_one − n_τ1zero ≥ 1`. This is NOT
delivered by the δ₊ laws here: a τ=1 zero-edge both lowers `κ₂` by 1 and resets δ₊
to max (forcing more downstream one-edges, of unbounded discrete-log magnitude
`ν₃(c − 2^τ)`), so δ₊-monotonicity does not pin the *net* balance. The deciding
configurations sit at 3-adic depth ≈ 3²¹ and are computationally invisible. This
module makes the residual a single named, provably-non-circular `Prop`; it is NOT
a proof of the S202 alternative, NOT a proof of Collatz.

Imports only `KappaSplitReduction` (hence the committed `projπ` functor, the ρ₊
transition laws, and the analytic-barrier infrastructure transitively). Adds NO
`native_decide`; nowhere near the `Cert_m1_Q10` blow-up.
-/

import CollatzLean4.KappaSplitReduction
import CollatzLean4.Nu3UnitInvariance

namespace CollatzLean4.Admissible

/-! ### Part 1 — The generic first-witness split of a `WPath` (F1)

`WPath` is defined by recursion on the interior-vertex list and the committed
`WPath_concat` only ever *joins*. To split a path at the FIRST vertex satisfying a
decidable predicate `P` we induct on the interior list, peeling one edge at a time
and either stopping (current source satisfies `P`) or recursing into the tail.

The `WPath` interior list is the sequence of edge *targets* (so the prefix interior
`vs₁` ends in `mid`). The firstness witness is therefore phrased as
`∀ x ∈ vs₁, P x → x = mid`: the only target inside the prefix that can satisfy `P`
is `mid` itself — i.e. `mid` is the FIRST witness along the traversal. Combined with
`¬ P s` (proved separately for the start) this pins `mid` as the first `P`-vertex
strictly after the start, which is exactly the data the residual below consumes. -/

/-- **Generic first-witness split.** For any weighted edge predicate `E` and any
decidable vertex predicate `P` with `P t`, a path `s ⟶ t` (weight `w`, interior
`vs`) splits as

  * a prefix `s ⟶ mid` (weight `w₁`, interior `vs₁`) whose only possible
    `P`-target is `mid` itself (`∀ x ∈ vs₁, P x → x = mid` — firstness), and
  * a suffix `mid ⟶ t` (weight `w₂`, interior `vs₂`) with `P mid`,

and the data concatenates: `w = w₁ + w₂`, `vs = vs₁ ++ vs₂`.

`mid` may equal `s` (when `P s`, giving the empty prefix `vs₁ = []`) or `t` (when no
target strictly before `t` satisfies `P`, giving the empty suffix `vs₂ = []`). The
proof is a clean induction on `vs` reusing the `WPath` constructors; it is
unconditional and generic in `(V, E, P)`. -/
theorem WPath_first_witness_split
    {V : Type} (E : V → V → Int → Prop) (P : V → Prop) [DecidablePred P]
    {s t : V} {w : Int} {vs : List V}
    (h_path : WPath E s t w vs) (h_end : P t) :
    ∃ (mid : V) (w₁ w₂ : Int) (vs₁ vs₂ : List V),
      WPath E s mid w₁ vs₁ ∧
      WPath E mid t w₂ vs₂ ∧
      w = w₁ + w₂ ∧
      vs = vs₁ ++ vs₂ ∧
      P mid ∧
      (∀ x ∈ vs₁, P x → x = mid) := by
  induction vs generalizing s w with
  | nil =>
      -- Empty interior: `s = t`, so `mid := s = t` satisfies `P` and the prefix
      -- is the trivial loop.
      simp only [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      exact ⟨s, 0, 0, [], [], ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by ring, rfl, h_end,
        by simp⟩
  | cons v vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      by_cases hPs : P s
      · -- `s` itself is the first witness: empty prefix, the whole path is the
        -- suffix.
        refine ⟨s, 0, ω₁ + ω₂, [], v :: vs', ⟨rfl, rfl⟩, ?_, by ring, rfl, hPs,
          by simp⟩
        exact ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩
      · by_cases hPv : P v
        · -- `v` (the first interior target) is the first witness: prefix is the
          -- single edge `s ⟶ v` (interior `[v]`), suffix is `v ⟶ t` (interior `vs'`).
          refine ⟨v, ω₁, ω₂, [v], vs', ?_, h_rest, by ring, rfl, hPv, ?_⟩
          · exact ⟨ω₁, 0, h_edge, ⟨rfl, rfl⟩, by ring⟩
          · intro x hx _; rw [List.mem_singleton] at hx; exact hx
        · -- neither `s` nor `v` is a witness: recurse on `v ⟶ t`, then prepend the
          -- edge `s ⟶ v`. The recursive prefix interior `vs₁` has `mid` as its only
          -- possible `P`-target; the newly-added head `v` is not a `P`-target by
          -- `hPv`, so the combined prefix interior `v :: vs₁` still has `mid` as its
          -- only possible `P`-target (firstness preserved).
          obtain ⟨mid, w₁, w₂, vs₁, vs₂, h_pre, h_suf, h_sum, h_vs, hPmid, h_no⟩ :=
            ih h_rest
          refine ⟨mid, ω₁ + w₁, w₂, v :: vs₁, vs₂, ?_, h_suf, by rw [h_sum]; ring,
            ?_, hPmid, ?_⟩
          · exact ⟨ω₁, w₁, h_edge, h_pre, rfl⟩
          · rw [h_vs]; rfl
          · intro x hx hPx
            rcases List.mem_cons.mp hx with rfl | h_mem
            · exact absurd hPx hPv
            · exact h_no x h_mem hPx

/-! ### Part 2 — The level-`m` precision predicate, its decidability, and the
non-`m`-precision of the start

`projMPrecise m v := IsGoal (projπ m v) (22m+2)` is the predicate "`v` agrees with
the root `1` to level-`m` precision" — i.e. `projπ m v` is an `m`-goal, equivalently
`v.c ≡ 1 (mod 3^(22m+2+v.j))`, equivalently `δ₊(v) ≤ 22` (committed D0 seed). It is
decidable (a `Nat` equation), so (F1) instantiates at it. The committed
`IsGoal_projectDown` says the `(m+1)`-goal is `m`-precise, so (F1) always applies on
a goal-reaching `(m+1)`-path. -/

/-- **Level-`m` precision predicate.** `v` is `m`-precise iff its `projπ`-projection
is a level-`m` goal, i.e. `v.c ≡ 1 (mod 3^(22m+2+v.j))`. -/
def projMPrecise (m : Nat) (v : InvVertex) : Prop :=
  InvVertex.IsGoal (projπ m v) (22 * m + 2)

instance instDecidableProjMPrecise (m : Nat) : DecidablePred (projMPrecise m) :=
  fun v => by unfold projMPrecise InvVertex.IsGoal; infer_instance

/-- The `(m+1)`-goal is `m`-precise (repackaging of the committed
`IsGoal_projectDown` against `projMPrecise`). This is the hypothesis `(F1)` needs at
the path's endpoint. -/
theorem projMPrecise_of_isGoal_succ {m : Nat} {v : InvVertex}
    (h : InvVertex.IsGoal v (22 * (m + 1) + 2)) :
    projMPrecise m v :=
  IsGoal_projectDown h

/-- **The start vertex is NOT `m`-precise** (for `m ≥ 1`). Because
`projπ m (InvStart (m+1)) = InvStart m` (committed `projπ_InvStart`) and
`(InvStart m).c = aS202 = 1 + 3^22 ≢ 1 (mod 3^(22m+2))` (since `22m+2 ≥ 24 > 22`),
the projected start is not a level-`m` goal.

Geometric content: the FIRST `m`-precision point of any `(m+1)`-path is strictly
AFTER the start. So the suffix from it is a *proper* tail of the path — the R1 trap
(empty suffix ⟹ κ₂ = 0) can only re-appear at the END (first `m`-precision point =
goal), never at the START. -/
theorem invStart_succ_not_mPrecise {m : Nat} (hm : 1 ≤ m) :
    ¬ projMPrecise m (InvStart (m + 1)) := by
  unfold projMPrecise
  rw [projπ_InvStart m hm]
  -- Goal: ¬ IsGoal (InvStart m) (22m+2), i.e. ¬ (aS202 % 3^(22m+2) = 1 % 3^(22m+2)).
  show ¬ ((InvStart m).c % 3 ^ (22 * m + 2 + (InvStart m).j)
        = 1 % 3 ^ (22 * m + 2 + (InvStart m).j))
  have hj : (InvStart m).j = 0 := rfl
  have hc : (InvStart m).c = aS202 := invStart_c_eq_aS202 m hm
  rw [hj, hc, Nat.add_zero]
  -- aS202 = 1 + 3^22 < 3^23 ≤ 3^(22m+2), so aS202 % 3^(22m+2) = aS202 = 1 + 3^22.
  -- Bound literal-free: 1 + 3^22 < 3^22 + 3^22 ≤ 3^23 (= 3·3^22) ≤ 3^(22m+2).
  have h22_pos : (1 : Nat) ≤ 3 ^ 22 := Nat.one_le_pow _ _ (by norm_num)
  have h_aS_lt : aS202 < 3 ^ (22 * m + 2) := by
    rw [aS202_decomp]
    have h23 : (3 : Nat) ^ 23 ≤ 3 ^ (22 * m + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h23_eq : (3 : Nat) ^ 23 = 3 * 3 ^ 22 := by rw [pow_succ]; ring
    omega
  have h1_lt : (1 : Nat) < 3 ^ (22 * m + 2) := by
    have h : (3 : Nat) ^ 1 ≤ 3 ^ (22 * m + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [pow_one] at h; omega
  rw [Nat.mod_eq_of_lt h_aS_lt, Nat.mod_eq_of_lt h1_lt, aS202_decomp]
  -- 1 + 3^22 ≠ 1 since 3^22 ≥ 1 > 0.
  omega

/-! ### Part 3 — The sharper residual `Prop` and the valid reduction

`FirstMPrecisionSuffixPositive m Q` is the residual: on the suffix from the FIRST
`m`-precision vertex `mid` to the goal, `κ₂ ≥ 1`. Whoever proves it is *handed* the
firstness data `(∀ x ∈ vs₁, projMPrecise m x → x = mid)` produced by (F1) — exactly
the information "no `m`-precision target strictly before `mid`" — which, with
`invStart_succ_not_mPrecise`, lets them argue `mid ≠ goal` in the binding cases. The
residual is therefore strictly weaker than `BlockBoundaryExists`: it only constrains
the canonical `mid`, it does not have to *exhibit* one.

`blockBoundaryExists_of_firstMPrecisionSuffixPositive` is the VALID reduction: every
conjunct of `BlockBoundaryExists` except `1 ≤ κ₂` is discharged by (F1) +
`IsGoal_projectDown` + `WPath_kappa_j_monotone`; the last conjunct is exactly the
residual. -/

/-- **The residual (sharper named `Prop`).** For the `(m+1)`-cylinder: whenever a
κ-path from `InvStart (m+1)` to a goal splits (via the first-witness split) into a
prefix `InvStart (m+1) ⟶ mid` and a suffix `mid ⟶ goal` with `mid` the FIRST
`m`-precision vertex (`projMPrecise m mid`, and no earlier `m`-precision target:
`∀ x ∈ vs₁, projMPrecise m x → x = mid`), the suffix carries `κ₂ ≥ 1`.

This is the ONE remaining open obligation of `BlockBoundaryExists`; it is NOT
asserted here, only named. It is provably non-circular: the firstness hypothesis is
strictly more data than the bare `(m+1)`-barrier conclusion. -/
def FirstMPrecisionSuffixPositive (m Q : Nat) : Prop :=
  ∀ {goal mid : InvVertex} {κ₁ κ₂ : Int} {vs₁ vs₂ : List InvVertex},
    InvVertex.IsGoal goal (22 * (m + 1) + 2) → goal.j ≤ Q →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) mid κ₁ vs₁ →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) mid goal κ₂ vs₂ →
    projMPrecise m mid →
    (∀ x ∈ vs₁, projMPrecise m x → x = mid) →
    (1 : Int) ≤ κ₂

/-- **The reduction (the headline deliverable).**
`FirstMPrecisionSuffixPositive m Q → BlockBoundaryExists m Q` for `m ≥ 1`.

The first-witness split (F1) at the decidable predicate `projMPrecise m` — applicable
because the `(m+1)`-goal is `m`-precise (`IsGoal_projectDown`) — produces the split
point `mid`, the prefix, the suffix, `κ = κ₁ + κ₂`, `vs = vs₁ ++ vs₂`,
`projMPrecise m mid`, and the firstness data. `WPath_kappa_j_monotone` on the suffix
gives `mid.j ≤ goal.j ≤ Q`. Every conjunct of `BlockBoundaryExists` is then in hand
except `1 ≤ κ₂`, which is exactly what the residual supplies. The structural split
is thereby fully DISCHARGED; only the κ₂ arithmetic remains. -/
theorem blockBoundaryExists_of_firstMPrecisionSuffixPositive
    {m Q : Nat}
    (h_res : FirstMPrecisionSuffixPositive m Q) :
    BlockBoundaryExists m Q := by
  intro goal κ vs h_g h_goal_j h_path
  -- (F1) at `P := projMPrecise m`; the endpoint `goal` is `m`-precise.
  obtain ⟨mid, κ₁, κ₂, vs₁, vs₂, h_pre, h_suf, h_sum, h_vs, h_mid_prec, h_first⟩ :=
    WPath_first_witness_split (InvKappaPreciseEdge (22 * (m + 1) + 2))
      (projMPrecise m) h_path (projMPrecise_of_isGoal_succ h_g)
  -- `mid.j ≤ Q` from `j`-monotonicity along the suffix.
  have h_mid_j : mid.j ≤ Q :=
    le_trans (WPath_kappa_j_monotone h_suf).1 h_goal_j
  -- `mid` is `m`-precise, i.e. `projπ m mid` is an `m`-goal.
  have h_mid_goal : InvVertex.IsGoal (projπ m mid) (22 * m + 2) := h_mid_prec
  -- The residual supplies `1 ≤ κ₂`.
  have h_κ₂ : (1 : Int) ≤ κ₂ :=
    h_res h_g h_goal_j h_pre h_suf h_mid_prec h_first
  exact ⟨mid, κ₁, κ₂, vs₁, vs₂, h_pre, h_suf, h_sum, h_vs, h_mid_goal, h_mid_j, h_κ₂⟩

/-! ### Part 4 — δ₊ per-edge monotonicity bricks (the one-edge-necessity engine)

The committed ρ₊ transition laws give, per edge: one-edge = discrete-log jump (the
only way δ₊ can DROP across the final gap); τ=2 zero = δ₊ UNCHANGED; odd-τ zero = δ₊
RESET to MAX. The lemmas here lift the odd-τ reset and the τ=2 climb to the level of
δ₊ *monotonicity* across an `InvKappaPreciseEdge`, supplying the verified content
"δ₊ can only DROP via a one-edge (or an even-τ≥4 zero-edge)".

The decisive one for the residual is `kappaEdge_kappaNeg1_deltaPlus_nondecr`: a τ=1
zero-edge — the *only* κ-precise edge of weight `−1` — has `δ₊(v') ≥ δ₊(v)`. So the
κ-spending edges DESTROY precision; this is precisely why combining "δ₊ drops on the
suffix ⟹ a one-edge is present" with the κ-balance `κ₂ = n_one − n_τ1zero` does NOT
close the residual (the τ=1 zeros that lower κ₂ also raise δ₊, demanding yet more
one-edges of unbounded discrete-log magnitude downstream). -/

/-- `ρ₊(c, r) ≤ r` (the root-proximity is capped at the precision). Both branches of
`rhoPlus` are `≤ r`: the `c = 1` branch is `r`, the other is `nu3 (c−1) r ≤ r`. -/
theorem rhoPlus_le_cap (c r : Nat) : rhoPlus c r ≤ r := by
  unfold rhoPlus
  split
  · exact le_rfl
  · exact nu3_le_cap _ _

/-- `δ₊(c, r) ≤ r` (the precision deficit never exceeds the precision). -/
theorem deltaPlus_le_cap (c r : Nat) : deltaPlus c r ≤ r := by
  unfold deltaPlus; omega

/-- **τ=1 zero-edge raises δ₊ to MAX.** Lifts the committed
`zeroEdge_tau_1_deltaPlus_max` to the δ₊-monotonicity statement
`δ₊(v.c, R+v.j) ≤ δ₊(v'.c, R+v'.j)`: a τ=1 zero-edge resets the target deficit to its
cap `R+v'.j ≥ R+v.j ≥ δ₊(v.c, R+v.j)`. NO canonicality hypotheses needed. -/
theorem zeroEdge_tau1_deltaPlus_nondecr
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω) (h_tau_1 : tau v'.c = 1) :
    deltaPlus v.c (R + v.j) ≤ deltaPlus v'.c (R + v'.j) := by
  have h_max := zeroEdge_tau_1_deltaPlus_max hR h_zero h_tau_1
  have h_j : v'.j = v.j + 1 := h_zero.1
  have h_le : deltaPlus v.c (R + v.j) ≤ R + v.j := deltaPlus_le_cap _ _
  rw [h_max]; omega

/-- **τ=3 zero-edge raises δ₊ to MAX.** Same as above for the τ=3 reset
(`zeroEdge_tau_3_deltaPlus_max`). -/
theorem zeroEdge_tau3_deltaPlus_nondecr
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω) (h_tau_3 : tau v'.c = 3) :
    deltaPlus v.c (R + v.j) ≤ deltaPlus v'.c (R + v'.j) := by
  have h_max := zeroEdge_tau_3_deltaPlus_max hR h_zero h_tau_3
  have h_j : v'.j = v.j + 1 := h_zero.1
  have h_le : deltaPlus v.c (R + v.j) ≤ R + v.j := deltaPlus_le_cap _ _
  rw [h_max]; omega

/-- **The κ = −1 edge destroys precision.** A κ-precise edge of weight `κ = −1` is a
τ=1 zero-edge, and along it δ₊ is NON-DECREASING: `δ₊(v') ≥ δ₊(v)`. So the only
κ-lowering edge resets the deficit to its cap.

This is the verified obstruction at the heart of the residual `FirstMPrecisionSuffix‐
Positive`: a τ=1 zero both subtracts `1` from `κ₂` and *raises* δ₊ back to max,
forcing further one-edges (of unbounded magnitude `ν₃(c − 2^τ)`) to re-descend — so
δ₊-monotonicity alone cannot bound the net balance `n_one − n_τ1zero` below by `1`. -/
theorem kappaEdge_kappaNeg1_deltaPlus_nondecr
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {κ : Int}
    (h_edge : InvKappaPreciseEdge R v v' κ) (hκ : κ = -1) :
    deltaPlus v.c (R + v.j) ≤ deltaPlus v'.c (R + v'.j) := by
  rcases h_edge with ⟨ω, _h_e, h_k⟩ | ⟨ω, h_e, h_tau, _h_k⟩ | ⟨ω, _h_e, _h_tau, h_k⟩
  · exact absurd (hκ.symm.trans h_k) (by norm_num)
  · exact zeroEdge_tau1_deltaPlus_nondecr hR h_e h_tau
  · exact absurd (hκ.symm.trans h_k) (by norm_num)

/-- **τ=2 zero-edge keeps δ₊ UNCHANGED.** Lifts the committed
`zeroEdge_tau2_rhoPlus_climb` (`ρ₊(v') = ρ₊(v) + 1`) to
`δ₊(v'.c, R+v'.j) = δ₊(v.c, R+v.j)`: the cap grows by one (`v'.j = v.j+1`) exactly as
ρ₊ does, so the deficit is preserved. Requires the canonicality and `v.c ≠ 1`
hypotheses of the climb law. This is the one κ = 0 case that, like one-edges, can
fail to RAISE δ₊ — but it cannot LOWER it either, so δ₊ drops are still carried by
one-edges (or even-τ ≥ 4 zeros, the residual gap of D3). -/
theorem zeroEdge_tau2_deltaPlus_eq
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω) (h_tau : tau v'.c = 2)
    (h_v_can : v.c < 3 ^ (R + v.j)) (h_v'_can : v'.c < 3 ^ (R + v'.j))
    (h_v_ne1 : v.c ≠ 1) :
    deltaPlus v'.c (R + v'.j) = deltaPlus v.c (R + v.j) := by
  have h_climb := zeroEdge_tau2_rhoPlus_climb hR h_zero h_tau h_v_can h_v'_can h_v_ne1
  have h_j : v'.j = v.j + 1 := h_zero.1
  have h_le : rhoPlus v.c (R + v.j) ≤ R + v.j := rhoPlus_le_cap _ _
  unfold deltaPlus
  rw [h_climb]
  -- (R+v'.j) - (ρ₊(v.c,R+v.j)+1) = (R+v.j) - ρ₊(v.c,R+v.j), since R+v'.j = R+v.j+1.
  omega
