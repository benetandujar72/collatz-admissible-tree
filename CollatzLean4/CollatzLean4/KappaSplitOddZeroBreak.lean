/-
**Odd-τ zero-edges destroy m-precision (the verified kernel of the κ₂-balance
argument, and the precise reason the naïve "no τ=1 zeros on the suffix"
argument is INCOMPLETE).**

Context (S238, `KappaSplitReduction.lean`). The single open core of the
uniform-in-`m` slope barrier is `BlockBoundaryExists m Q`: every level-`(m+1)`
κ-path `InvStart(m+1) → goal` splits at a `mid` with `projπ m mid` an `m`-goal
(*m-precision*) **and** suffix `κ₂ ≥ 1`. A tempting strategy is:

  "Take `mid` = the last m-precision point; the suffix to the goal cannot contain
   τ=1 zero-edges (they reset ρ₊, destroying m-precision), so the suffix κ₂
   counts only one-edges and is ≥ 1."

This module isolates the ONE rigorous, build-verified fact behind that strategy —
and, by stating it exactly, exposes why the strategy does **not** close the core.

  * `oddZeroEdge_breaks_mPrecision` — the target `v'` of any τ∈{1,3} inverse
    zero-edge has `projπ m v'` **not** an `m`-goal, for every `m`. (Because the
    consistency clause forces `v'.c ≡ 2 (mod 3)`, while an `m`-goal needs
    `v'.c ≡ 1 (mod 3^(22m+2+v'.j))`, and `3 ∣ 3^(22m+2+v'.j)`.)

  * `mPrecision_not_target_of_oddZero` — contrapositive: an `m`-precise vertex is
    never the target of a τ∈{1,3} zero-edge.

**Why this does NOT finish `BlockBoundaryExists` (honest scope).** The lemma
constrains only the *endpoints*: an m-precise vertex is not *immediately
preceded* by a τ∈{1,3} zero-edge. It says nothing that forbids τ=1 zero-edges in
the *interior* of a suffix whose endpoints are m-precise — interior vertices are
allowed (indeed forced) to be non-m-precise, so τ=1 zeros sit there freely. Hence
the suffix balance `κ₂ = (#one) − (#τ1-zero)` is NOT pinned to `≥ 1` by this
fact. Moreover the dominant obstruction found by the S238 probes is orthogonal to
τ=1 zeros entirely: a single deep ONE-edge (`oneEdge_rhoPlus_law`,
`ρ₊(c') = ν₃(c − 2^τ)`) can lift ρ₊ across BOTH the coarse (`22m+2`) and fine
(`22m+24`) thresholds at once, so the *first* m-precision point on a path can be
the goal itself — leaving only the trivial split `κ₂ = 0` (the `R1` trap,
`outerBlockIncrement_false`). This module therefore records a TRUE sub-lemma and
the precise scope of its insufficiency; it CLOSES nothing new. 0 sorry.
-/

import CollatzLean4.KappaSplitWork
import CollatzLean4.RhoTransitionLaws

namespace CollatzLean4.Admissible

/-- **Odd-τ zero-edges break m-precision.** If `v'` is the target of a τ∈{1,3}
inverse zero-edge (base precision `R ≥ 1`), then `projπ m v'` is **not** a
level-`m` goal, for every `m`.

Proof. The τ∈{1,3} consistency clause forces `v'.c ≡ 2 (mod 3)`
(`zeroEdge_tau_1_vc_mod3` / `zeroEdge_tau_3_vc_mod3`). An `m`-goal of `projπ m v'`
is exactly `v'.c ≡ 1 (mod 3^(22m+2+v'.j))` (after the idempotent `projπ` mod).
Reducing that congruence further mod `3` (valid since `3 ∣ 3^(22m+2+v'.j)`) would
give `v'.c ≡ 1 (mod 3)`, contradicting `v'.c ≡ 2 (mod 3)`. -/
theorem oddZeroEdge_breaks_mPrecision
    {R : Nat} (hR : 1 ≤ R) (m : Nat) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau : tau v'.c = 1 ∨ tau v'.c = 3) :
    ¬ InvVertex.IsGoal (projπ m v') (22 * m + 2) := by
  -- v'.c ≡ 2 (mod 3) in both odd-τ cases.
  have h_mod3 : v'.c % 3 = 2 := by
    rcases h_tau with h1 | h3
    · exact zeroEdge_tau_1_vc_mod3 hR h_zero h1
    · exact zeroEdge_tau_3_vc_mod3 hR h_zero h3
  intro h_goal
  -- Unfold the projected goal to a plain congruence on v'.c at the m-cap.
  -- `IsGoal (projπ m v') (22m+2)` is, definitionally,
  --   (projπ m v').c % 3^(22m+2+(projπ m v').j) = 1 % 3^(22m+2+(projπ m v').j)
  -- and `(projπ m v').j = v'.j`, `(projπ m v').c = v'.c % 3^(22m+2+v'.j)`.
  set P := 3 ^ (22 * m + 2 + v'.j) with hP
  have h_goal0 : (v'.c % P) % P = 1 % P := by
    have h : (projπ m v').c % 3 ^ (22 * m + 2 + (projπ m v').j)
           = 1 % 3 ^ (22 * m + 2 + (projπ m v').j) := h_goal
    simpa only [projπ_j, projπ_c, hP] using h
  have h_goal' : v'.c % P = 1 % P := by rw [Nat.mod_mod] at h_goal0; exact h_goal0
  -- h_goal' : v'.c % P = 1 % P, i.e. v'.c ≡ 1 (mod P).
  -- Reduce further mod 3 (3 ∣ P).
  have h3dvdP : (3 : Nat) ∣ P := by
    rw [hP]; exact dvd_pow_self 3 (by omega : 22 * m + 2 + v'.j ≠ 0)
  have hL := Nat.mod_mod_of_dvd v'.c h3dvdP
  have hRr := Nat.mod_mod_of_dvd (1 : Nat) h3dvdP
  have h_mod3' : v'.c % 3 = 1 % 3 := by
    rw [← hL, h_goal', hRr]
  -- But v'.c % 3 = 2 and 1 % 3 = 1: contradiction.
  rw [h_mod3] at h_mod3'
  norm_num at h_mod3'

/-- **Contrapositive form.** A level-`m`-precise vertex (one whose `projπ`-image
is an `m`-goal) is never the target of a τ∈{1,3} inverse zero-edge. This is the
exact, and ONLY, structural constraint the "last m-precision point" heuristic
supplies: m-precision cannot be the *immediate successor* of an odd-τ zero-edge.
It does not constrain odd-τ zeros in the interior of an m-precise-to-m-precise
suffix, which is why it does not by itself yield `κ₂ ≥ 1`. -/
theorem mPrecision_not_target_of_oddZero
    {R : Nat} (hR : 1 ≤ R) (m : Nat) {v v' : InvVertex} {ω : Int}
    (h_prec : InvVertex.IsGoal (projπ m v') (22 * m + 2))
    (h_zero : InvEdgeZero R v v' ω) :
    tau v'.c ≠ 1 ∧ tau v'.c ≠ 3 := by
  constructor
  · intro h1
    exact oddZeroEdge_breaks_mPrecision hR m h_zero (Or.inl h1) h_prec
  · intro h3
    exact oddZeroEdge_breaks_mPrecision hR m h_zero (Or.inr h3) h_prec

end CollatzLean4.Admissible
