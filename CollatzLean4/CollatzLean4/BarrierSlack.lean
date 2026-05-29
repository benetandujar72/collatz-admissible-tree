/-
**Astronomical slackness of the S202 slope barrier (LTE-driven lower bound on `A`).**

This module formalizes the *quantitative* content behind the slogan

  "the barrier `n_one − n_neg ≥ m` is astronomically slack":

reaching the deep `m = 1` S202 cylinder is governed by a 3-adic *discrete
logarithm*, and whenever the relevant valuation equals `22` (the exact value
`ν₃(aS202 − 1) = ν₃(3^22) = 22`, see `S202Cylinders.aS202_sub_one`), the
accumulated word exponent `A` is forced — via lifting-the-exponent — to be
*astronomically large*:

      ν₃(2^A − 1) = 22   ⟹   A ≥ 2 · 3^21 = 20 920 706 406.

The number `2·3^21 ≈ 2.09 × 10^10` is the rigorous source of "slack": even the
*first* non-trivial cylinder cannot be reached by any short word; the exponent
budget is pinned ten orders of magnitude above any naive expectation.

STRUCTURE.

  * **Part A — pure LTE (UNCONDITIONAL, fully proven).** From the closed form
    `ν₃(2^S − 1) = (Even S ? 1 + ν₃(S) : 0)` (proved in `LTEBound.lean`) we
    derive, with no extra hypotheses:
      - `even_of_valuation_two_pow_sub_one_pos`  : `ν₃(2^A−1) ≥ 1 ⟹ Even A`;
      - `dvd_of_valuation_two_pow_sub_one`       : `ν₃(2^A−1) = v ≥ 1 ⟹ 2·3^(v−1) ∣ A`;
      - `slackness_from_valuation`               : `… ⟹ A ≥ 2·3^(v−1)`;
      - `slackness_at_22`                        : `ν₃(2^A−1) = 22 ⟹ A ≥ 2·3^21`.
    These are complete, build-verified theorems about the 3-adic valuation.

  * **Part B — the word→valuation bridge (CONDITIONAL; the residual gap).**
    The genuinely open step is to *derive* `ν₃(2^A − 1) = 22` from the cylinder
    condition `(evalWord u).n ≡ aS202 (mod 3^24)`. We isolate this single
    missing implication as a named predicate `CylinderForcesVal22` and prove
    the conditional corollary `cylinder_forces_astronomical_A`: under that
    bridge, every word reaching the `m=1` cylinder has `A ≥ 2·3^21`. The bridge
    itself is NOT proved here (and cannot be closed by the existing machinery —
    see HONEST SCOPE), so it is stated as a hypothesis, never as an `axiom`.

HONEST SCOPE. Part A is unconditional and complete. Part B is conditional on an
explicitly-stated bridge hypothesis. This is NOT a proof of Collatz, nor of the
full S202 alternative; it quantifies the *slackness* of one barrier on the
slope-barrier sub-route, and pinpoints the exact remaining gap (the cylinder →
`ν₃(2^A−1)` bridge). The repository's actual S202 route converts the cylinder
condition into an additive *defect* `A − 2q` bound, not a 3-adic constraint on
`A` in isolation; the `2^A` side is a 3-adic unit (`ν₃(2^A) = 0`), so any
direct valuation statement about `A` must pass through a `2^A − (·)` quantity,
which is exactly what the bridge would supply.
-/

import CollatzLean4.LTEBound
import CollatzLean4.S202Cylinders

namespace CollatzLean4.Admissible

open scoped Classical

/-! ## Part A — pure lifting-the-exponent: slackness from the valuation

Everything here is unconditional and uses only `LTEBound.padicValNat_two_pow_sub_one`
and standard Mathlib 3-adic API. -/

/-- If the 3-adic valuation of `2^A − 1` is positive, then `A` is **even**.
(For odd `A`, `2^A ≡ 2 (mod 3)`, so `3 ∤ 2^A − 1` and the valuation is `0`.) -/
theorem even_of_valuation_two_pow_sub_one_pos {A : ℕ}
    (hpos : 1 ≤ padicValNat 3 (2 ^ A - 1)) : Even A := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hzero : padicValNat 3 (2 ^ A - 1) = 0 := padicValNat_two_pow_sub_one_odd hodd
  omega

/-- **Core LTE slackness (divisibility form).** If `ν₃(2^A − 1) = v` with
`v ≥ 1`, then `2 · 3^(v−1)` divides `A`.

Proof. `v ≥ 1` forces `A` even (`even_of_valuation_two_pow_sub_one_pos`); the
even branch of the LTE closed form gives `v = 1 + ν₃(A)`, i.e. `ν₃(A) = v − 1`,
whence `3^(v−1) ∣ A` (`padicValNat_dvd_iff_le`). As `A` is even, `2 ∣ A`; since
`gcd(2, 3^(v−1)) = 1`, the two divisibilities combine to `2·3^(v−1) ∣ A`. -/
theorem dvd_of_valuation_two_pow_sub_one {A v : ℕ} (hA : A ≠ 0) (hv : 1 ≤ v)
    (hval : padicValNat 3 (2 ^ A - 1) = v) :
    2 * 3 ^ (v - 1) ∣ A := by
  -- `A` is even.
  have hpos : 1 ≤ padicValNat 3 (2 ^ A - 1) := by omega
  have heven : Even A := even_of_valuation_two_pow_sub_one_pos hpos
  -- LTE even branch: ν₃(2^A−1) = 1 + ν₃(A).
  have hLTE : padicValNat 3 (2 ^ A - 1) = 1 + padicValNat 3 A := by
    rw [padicValNat_two_pow_sub_one A hA, if_pos heven]
  -- Hence ν₃(A) = v − 1.
  have hvalA : padicValNat 3 A = v - 1 := by omega
  -- 3^(v−1) ∣ A.
  have h3 : (3 : ℕ) ^ (v - 1) ∣ A := by
    rw [padicValNat_dvd_iff_le hA, hvalA]
  -- 2 ∣ A.
  have h2 : (2 : ℕ) ∣ A := heven.two_dvd
  -- combine via coprimality of 2 and 3^(v−1).
  have hcop : Nat.Coprime 2 (3 ^ (v - 1)) :=
    Nat.Coprime.pow_right _ (by decide)
  exact hcop.mul_dvd_of_dvd_of_dvd h2 h3

/-- **Core LTE slackness (lower-bound form).** If `ν₃(2^A − 1) = v` with
`v ≥ 1`, then `A ≥ 2 · 3^(v−1)`. Immediate from the divisibility form and
`A ≠ 0`. -/
theorem slackness_from_valuation {A v : ℕ} (hA : A ≠ 0) (hv : 1 ≤ v)
    (hval : padicValNat 3 (2 ^ A - 1) = v) :
    2 * 3 ^ (v - 1) ≤ A := by
  have hdvd : 2 * 3 ^ (v - 1) ∣ A :=
    dvd_of_valuation_two_pow_sub_one hA hv hval
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hA) hdvd

/-- **Headline slackness bound.** If `ν₃(2^A − 1) = 22` — the value forced at
the `m = 1` S202 cylinder, since `ν₃(aS202 − 1) = ν₃(3^22) = 22` — then

      A ≥ 2 · 3^21 = 20 920 706 406 ≈ 2.09 × 10^10.

This is the rigorous, fully-proven form of "the barrier is astronomically
slack": the word exponent is pinned ten orders of magnitude up. -/
theorem slackness_at_22 {A : ℕ} (hA : A ≠ 0)
    (hval : padicValNat 3 (2 ^ A - 1) = 22) :
    2 * 3 ^ 21 ≤ A := by
  have h := slackness_from_valuation (v := 22) hA (by norm_num) hval
  simpa using h

/-- The explicit decimal value of the slackness bound: `2 · 3^21 = 20920706406`.
Bundled so downstream statements can quote the concrete astronomical figure. -/
theorem slackness_at_22_value {A : ℕ} (hA : A ≠ 0)
    (hval : padicValNat 3 (2 ^ A - 1) = 22) :
    20920706406 ≤ A := by
  have h := slackness_at_22 hA hval
  norm_num at h
  exact h

/-! ## Part B — the word→valuation bridge (conditional; residual gap)

The unconditional Part A says: *once* the valuation `ν₃(2^A − 1)` is known to be
`22`, the exponent is astronomically large. What remains genuinely open is the
*bridge*: deriving `ν₃(2^A − 1) = 22` from the cylinder membership of a word.

We do NOT prove that bridge (it cannot be discharged by the existing word
semantics — the cylinder controls `n mod 3^24`, while `2^A` is a 3-adic unit;
the link `B ≡ 2^A (mod 3^q)` is the only valuation fact available, and it does
not by itself pin `ν₃(2^A − 1)`). We isolate it as a named hypothesis so the
implication "bridge ⟹ astronomical slack" is itself a checked theorem. -/

/-- **The residual bridge, named.** `CylinderForcesVal22` asserts exactly the
unproven implication: every word `u` landing in the `m = 1` S202 cylinder
(`(evalWord u).n ≡ aS202 (mod 3^24)`) and performing at least one step
(`(evalWord u).A ≠ 0`) has `ν₃(2^(A(u)) − 1) = 22`.

This is the *only* gap between the repository's word semantics and the
astronomical lower bound of Part A. It is stated as a `Prop`, never assumed as
an `axiom`. -/
def CylinderForcesVal22 : Prop :=
  ∀ u : Word,
    (evalWord u).n % (3 ^ 24) = aS202 % (3 ^ 24) →
    (evalWord u).A ≠ 0 →
    padicValNat 3 (2 ^ (evalWord u).A - 1) = 22

/-- **Conditional astronomical-slackness theorem.** *Assuming* the bridge
`CylinderForcesVal22`, every non-trivial word reaching the `m = 1` S202 cylinder
has accumulated exponent `A ≥ 2·3^21 = 20920706406`.

This is the formal statement "reaching the m=1 cylinder forces an astronomically
huge word valuation `A`", reduced to the single explicit bridge hypothesis. -/
theorem cylinder_forces_astronomical_A
    (bridge : CylinderForcesVal22)
    (u : Word)
    (h_cyl : (evalWord u).n % (3 ^ 24) = aS202 % (3 ^ 24))
    (h_nontrivial : (evalWord u).A ≠ 0) :
    2 * 3 ^ 21 ≤ (evalWord u).A := by
  have hval : padicValNat 3 (2 ^ (evalWord u).A - 1) = 22 :=
    bridge u h_cyl h_nontrivial
  exact slackness_at_22 h_nontrivial hval

/-- Decimal restatement of the conditional theorem: under the bridge, the
exponent of any non-trivial word in the `m = 1` cylinder is at least
`20 920 706 406`. -/
theorem cylinder_forces_astronomical_A_value
    (bridge : CylinderForcesVal22)
    (u : Word)
    (h_cyl : (evalWord u).n % (3 ^ 24) = aS202 % (3 ^ 24))
    (h_nontrivial : (evalWord u).A ≠ 0) :
    20920706406 ≤ (evalWord u).A := by
  have h := cylinder_forces_astronomical_A bridge u h_cyl h_nontrivial
  norm_num at h
  exact h

/-! ### Sanity anchor: the cylinder valuation target really is `22`

The bridge's target value `22` is not arbitrary: it is exactly the 3-adic
distance `ν₃(aS202 − 1)`, which the repository already pins via
`aS202_sub_one : aS202 − 1 = 3^22`. We record the capped-`nu3` and uncapped
`padicValNat` forms of `ν₃(aS202 − 1) = 22` to document that `22` in
`CylinderForcesVal22` is the structurally-correct constant. -/

/-- `ν₃(aS202 − 1) = 22` (uncapped Mathlib valuation), the structural origin of
the `22` appearing in the bridge target. From `aS202 − 1 = 3^22`. -/
theorem padicValNat_aS202_sub_one : padicValNat 3 (aS202 - 1) = 22 := by
  rw [aS202_sub_one]
  -- padicValNat 3 (3^22) = 22  (Fact (Nat.Prime 3) found automatically)
  exact padicValNat.prime_pow (p := 3) 22

/-- The capped project valuation also reads `22` at any cap `> 22`, via the
`LTEBound` bridge `nu3_eq_padicValNat_of_lt`. Documents agreement of the two
valuation notions on the cylinder coordinate. -/
theorem nu3_aS202_sub_one (c : ℕ) (hc : 22 < c) : nu3 (aS202 - 1) c = 22 := by
  have hne : aS202 - 1 ≠ 0 := by rw [aS202_sub_one]; positivity
  rw [nu3_eq_padicValNat_of_lt _ c hne (by rw [padicValNat_aS202_sub_one]; exact hc),
      padicValNat_aS202_sub_one]

end CollatzLean4.Admissible
