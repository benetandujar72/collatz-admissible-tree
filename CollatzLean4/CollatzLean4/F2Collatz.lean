/-
S243 — The function-field Collatz twin, part I: the map and the EXACT degree laws.

The control experiment identified by the S241 bridge scoping: the Collatz analogue on
`𝔽₂[x]` (Hicks–Mullen–Yucas–Zavislak, *Amer. Math. Monthly* 115(7), 2008) —

    `T(f) = f / x`  if `f(0) = 0`,    `T(f) = (x+1)·f + 1`  if `f(0) = 1`

— is a THEOREM: every nonzero `f` reaches `1`.  The reason it is a theorem while the
integer problem is open is precisely that **degree has no carries**: where the integer
size laws are lossy (`size(3n+1) ≥ size(n) + 1`, the slack driven by the archimedean
Sturmian carry process — see BitlenPotential.lean and the S241–S242 verdicts), the
degree laws are EXACT equalities.  This module formalizes part I (believed to be the
first formalization of this development in any proof assistant):

  * `oddStep_natDegree` — `deg((x+1)f + 1) = deg f + 1` EXACTLY (the carry-free twin
    of `size_three_mul_add_one`);
  * `oddStep_coeff_zero` — the odd step always lands even (the twin of "3n+1 is even");
  * `evenStep_natDegree` — `deg(f/x) = deg f − 1` (the twin of `size_two_pow_mul`);
  * `collatzT_ne_zero` — orbits never die;
  * `collatzT_iterate_natDegree_le` — **pointwise no-divergence**:
    `deg(T^[k] f) ≤ deg f + 1` for ALL `k` — the statement that provably does NOT hold
    for the integer size (where two worst-case steps can gain a bit).

Part II (next): the Frobenius plateau clock (`(1+x)^{2^k} = 1 + x^{2^k}`) and the
headline `collatz_F2X : ∀ f ≠ 0, ∃ k, T^[k] f = 1`.

Axioms target: {propext, Classical.choice, Quot.sound}.  Builds narrow.
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic

namespace CollatzLean4.F2

open Polynomial

/-- The polynomial ring `𝔽₂[x]`. -/
abbrev F2X := Polynomial (ZMod 2)

/-- Every element of `𝔽₂` is `0` or `1`. -/
theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

/-- **The HMYZ Collatz map on `𝔽₂[x]`**: divide by `x` when possible ("even"),
else multiply by `x+1` and add `1` ("odd"). -/
noncomputable def collatzT (f : F2X) : F2X :=
  if f.coeff 0 = 0 then f /ₘ X else (X + 1) * f + 1

/-- Even branch equation. -/
theorem collatzT_of_even {f : F2X} (h : f.coeff 0 = 0) : collatzT f = f /ₘ X := by
  unfold collatzT
  rw [if_pos h]

/-- Odd branch equation. -/
theorem collatzT_of_odd {f : F2X} (h : f.coeff 0 ≠ 0) :
    collatzT f = (X + 1) * f + 1 := by
  unfold collatzT
  rw [if_neg h]

/-! ### The two branches -/

theorem X_add_one_monic : (X + 1 : F2X).Monic := by
  rw [show (1 : F2X) = C 1 from C_1.symm]
  exact monic_X_add_C 1

theorem X_add_one_ne_zero : (X + 1 : F2X) ≠ 0 :=
  X_add_one_monic.ne_zero

theorem natDegree_X_add_one : (X + 1 : F2X).natDegree = 1 := by
  rw [show (1 : F2X) = C 1 from C_1.symm]
  exact natDegree_X_add_C 1

/-- The odd branch raises the degree by EXACTLY one (no carries). -/
theorem oddStep_natDegree {f : F2X} (h : f.coeff 0 = 1) :
    ((X + 1) * f + 1).natDegree = f.natDegree + 1 := by
  have hf : f ≠ 0 := by
    intro h0
    rw [h0, coeff_zero] at h
    exact one_ne_zero h.symm
  have hlc : (X + 1 : F2X).leadingCoeff * f.leadingCoeff ≠ 0 := by
    rw [X_add_one_monic.leadingCoeff, one_mul]
    exact leadingCoeff_ne_zero.mpr hf
  have hmul : ((X + 1) * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_mul' hlc, natDegree_X_add_one]
    omega
  calc ((X + 1) * f + 1).natDegree
      = ((X + 1) * f + C 1).natDegree := by rw [C_1]
    _ = ((X + 1) * f).natDegree := natDegree_add_C
    _ = f.natDegree + 1 := hmul

/-- The odd step always lands even: `((x+1)f + 1)(0) = 1·1 + 1 = 0` in `𝔽₂`. -/
theorem oddStep_coeff_zero {f : F2X} (h : f.coeff 0 = 1) :
    ((X + 1) * f + 1).coeff 0 = 0 := by
  simp only [coeff_add, mul_coeff_zero, coeff_X_zero, coeff_one_zero, h]
  decide

/-- The odd step output is nonzero. -/
theorem oddStep_ne_zero {f : F2X} (h : f.coeff 0 = 1) :
    (X + 1) * f + 1 ≠ 0 := by
  intro h0
  have hd := oddStep_natDegree h
  rw [h0, natDegree_zero] at hd
  omega

/-- The even branch lowers the degree by exactly one. -/
theorem evenStep_natDegree (f : F2X) :
    (f /ₘ X).natDegree = f.natDegree - 1 := by
  rw [natDegree_divByMonic f monic_X, natDegree_X]

/-- The even branch preserves nonzeroness (for even nonzero `f`). -/
theorem evenStep_ne_zero {f : F2X} (hf : f ≠ 0) (h : f.coeff 0 = 0) :
    f /ₘ X ≠ 0 := by
  intro h0
  have hdvd : X ∣ f := X_dvd_iff.mpr h
  have heq : X * (f /ₘ X) = f := by
    obtain ⟨g, hg⟩ := hdvd
    rw [hg, mul_divByMonic_cancel_left g monic_X]
  rw [h0, mul_zero] at heq
  exact hf heq.symm

/-! ### Nonzero preservation and the pointwise degree bound -/

/-- Orbits never die: `T f ≠ 0` for `f ≠ 0`. -/
theorem collatzT_ne_zero {f : F2X} (hf : f ≠ 0) : collatzT f ≠ 0 := by
  by_cases h : f.coeff 0 = 0
  · rw [collatzT_of_even h]
    exact evenStep_ne_zero hf h
  · rw [collatzT_of_odd h]
    rcases zmod2_cases (f.coeff 0) with h0 | h1
    · exact absurd h0 h
    · exact oddStep_ne_zero h1

/-- **Pointwise no-divergence** (the statement with NO integer counterpart): every
iterate satisfies `deg(T^[k] f) ≤ deg f + 1`.  Invariant: odd points sit at
`deg ≤ deg f`; the odd step raises the degree by exactly one but lands even, and the
even step lowers it. -/
theorem collatzT_iterate_natDegree_le (f : F2X) (hf : f ≠ 0) :
    ∀ k, (collatzT^[k] f).natDegree ≤ f.natDegree + 1 := by
  suffices h : ∀ k, (collatzT^[k] f) ≠ 0 ∧
      (collatzT^[k] f).natDegree ≤ f.natDegree + 1 ∧
      ((collatzT^[k] f).coeff 0 ≠ 0 → (collatzT^[k] f).natDegree ≤ f.natDegree) by
    intro k
    exact (h k).2.1
  intro k
  induction k with
  | zero =>
      simp only [Function.iterate_zero_apply]
      exact ⟨hf, by omega, fun _ => le_refl _⟩
  | succ k ih =>
      obtain ⟨hne, hdeg, hodd⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨collatzT_ne_zero hne, ?_⟩
      by_cases h0 : (collatzT^[k] f).coeff 0 = 0
      · -- even step: the degree drops by one
        rw [collatzT_of_even h0]
        have hev := evenStep_natDegree (collatzT^[k] f)
        exact ⟨by omega, fun _ => by omega⟩
      · -- odd step: degree +1 exactly, input was odd (≤ deg f), output is even
        rw [collatzT_of_odd h0]
        rcases zmod2_cases ((collatzT^[k] f).coeff 0) with ha | h1
        · exact absurd ha h0
        · have hstep := oddStep_natDegree h1
          have hgle := hodd h0
          refine ⟨by omega, fun hcontra => ?_⟩
          exact absurd (oddStep_coeff_zero h1) hcontra

end CollatzLean4.F2
