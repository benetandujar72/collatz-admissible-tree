/-
S243 — The function-field Collatz twin: the HMYZ theorem, fully formalized.

The control experiment identified by the S241 bridge scoping: the Collatz analogue on
`𝔽₂[x]` (Hicks–Mullen–Yucas–Zavislak, *Amer. Math. Monthly* 115(7), 2008) —

    `T(f) = f / x`  if `f(0) = 0`,    `T(f) = (x+1)·f + 1`  if `f(0) = 1`

— is a THEOREM: every nonzero `f` reaches `1`.  The reason it is a theorem while the
integer problem is open is precisely that **degree has no carries**: where the integer
size laws are lossy (`size(3n+1) ≥ size(n) + 1`, the slack driven by the archimedean
Sturmian carry process — see BitlenPotential.lean and the S241–S242 verdicts), the
degree laws are EXACT equalities.  This module formalizes the full development
(believed to be the first formalization in any proof assistant):

  * `oddStep_natDegree` — `deg((x+1)f + 1) = deg f + 1` EXACTLY (the carry-free twin
    of `size_three_mul_add_one`);
  * `oddStep_coeff_zero` — the odd step always lands even (the twin of "3n+1 is even");
  * `evenStep_natDegree` — `deg(f/x) = deg f − 1` (the twin of `size_two_pow_mul`);
  * `collatzT_ne_zero` — orbits never die;
  * `collatzT_iterate_natDegree_le` — **pointwise no-divergence**:
    `deg(T^[k] f) ≤ deg f + 1` for ALL `k` — the statement that provably does NOT hold
    for the integer size (where two worst-case steps can gain a bit).

Part II (this file, below): the PLATEAU TELESCOPE — sharper than the literature's
multiplicative-order/Frobenius argument.  In the `f+1` coordinate the two-step plateau
map is multiplication by `(x+1)/x` (`plateau_step_identity`), so each plateau step
consumes exactly one trailing factor `x` of `f+1` and the plateau exits in at most
`ord_x(f₀+1) − 1 ≤ deg f₀ − 1` steps (`plateau_exit`, pure ring algebra — no group
theory).  Headline: `collatz_F2X : ∀ f ≠ 0, ∃ k, T^[k] f = 1`.

Axioms target: {propext, Classical.choice, Quot.sound}.  Builds narrow.
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas

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


/-! ### Part II — the plateau telescope and the main theorem

The plateau (an odd `f` whose two-step image `T²f = ((x+1)f+1)/x` is odd again, at the
same degree) exits by a TELESCOPING identity, sharper than the literature's
multiplicative-order argument: in the `f+1` coordinate the plateau map is
multiplication by `(x+1)/x` —

    `x·(T²f + 1) = (x+1)·(f+1)`,

so each plateau step consumes exactly one factor `x` of `f+1`: after at most
`ord_x(f₀+1) − 1` steps the iterate is even (or has become `1`), and the degree drops.
Pure ring algebra; no group theory needed. -/

/-- Iterates of a nonzero polynomial are nonzero. -/
theorem collatzT_iterate_ne_zero {f : F2X} (hf : f ≠ 0) :
    ∀ k, collatzT^[k] f ≠ 0 := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact collatzT_ne_zero ih

/-- The two-step plateau map on odd `f`: `T²f = ((x+1)f + 1) /ₘ x`. -/
theorem collatzT_two_of_odd {f : F2X} (h : f.coeff 0 = 1) :
    collatzT^[2] f = ((X + 1) * f + 1) /ₘ X := by
  have h1 : collatzT f = (X + 1) * f + 1 :=
    collatzT_of_odd (by rw [h]; exact one_ne_zero)
  rw [Function.iterate_succ_apply', Function.iterate_one, h1,
      collatzT_of_even (oddStep_coeff_zero h)]

/-- The cancel identity: `x·(T²f) = (x+1)f + 1` (odd `f`). -/
theorem plateau_cancel {f : F2X} (h : f.coeff 0 = 1) :
    X * (collatzT^[2] f) = (X + 1) * f + 1 := by
  rw [collatzT_two_of_odd h]
  have hdvd : X ∣ (X + 1) * f + 1 := X_dvd_iff.mpr (oddStep_coeff_zero h)
  obtain ⟨g, hg⟩ := hdvd
  rw [hg, mul_divByMonic_cancel_left g monic_X]

/-- **The plateau telescope**: `x·(T²f + 1) = (x+1)·(f+1)` — the plateau map is
multiplication by `(x+1)/x` in the `f+1` coordinate. -/
theorem plateau_step_identity {f : F2X} (h : f.coeff 0 = 1) :
    X * (collatzT^[2] f + 1) = (X + 1) * (f + 1) := by
  have hc := plateau_cancel h
  calc X * (collatzT^[2] f + 1) = X * collatzT^[2] f + X := by ring
    _ = (X + 1) * f + 1 + X := by rw [hc]
    _ = (X + 1) * (f + 1) := by ring

theorem isCoprime_X_X_add_one : IsCoprime (X : F2X) (X + 1) :=
  ⟨-1, 1, by ring⟩

/-- A nonzero polynomial is not divisible by `x^{deg+1}` — the instance-light version
of `natDegree_le_of_dvd` (avoids `NoZeroDivisors`, same `natDegree_mul'` dodge as the
degree laws above). -/
theorem not_X_pow_natDegree_succ_dvd {g : F2X} (hg : g ≠ 0) :
    ¬ (X ^ (g.natDegree + 1) ∣ g) := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact hg hc
  have hlc : (X ^ (g.natDegree + 1) : F2X).leadingCoeff * c.leadingCoeff ≠ 0 := by
    rw [(monic_X_pow _).leadingCoeff, one_mul]
    exact leadingCoeff_ne_zero.mpr hc0
  have hdeg : g.natDegree = (g.natDegree + 1) + c.natDegree := by
    conv_lhs => rw [hc]
    rw [natDegree_mul' hlc, natDegree_X_pow]
  omega

/-- **The plateau exits**: an odd `f ≠ 1` with `¬ x^{v+1} ∣ (f+1)` reaches a strictly
smaller degree (induction on the trailing-multiplicity fuel `v`). -/
theorem plateau_exit : ∀ v : ℕ, ∀ f : F2X, f.coeff 0 = 1 → f ≠ 1 →
    ¬ (X ^ (v + 1) ∣ (f + 1)) →
    ∃ k, (collatzT^[k] f).natDegree < f.natDegree := by
  intro v
  induction v with
  | zero =>
      intro f hodd _ hdvd
      exfalso
      apply hdvd
      rw [pow_one]
      apply X_dvd_iff.mpr
      rw [coeff_add, hodd, coeff_one_zero]
      decide
  | succ v ih =>
      intro f hodd hne hdvd
      have hdeg1 : 1 ≤ f.natDegree := by
        by_contra hd
        have h0 : f.natDegree = 0 := by omega
        have hC := eq_C_of_natDegree_eq_zero h0
        rw [hodd, C_1] at hC
        exact hne hC
      set g := collatzT^[2] f with hgdef
      have hdegg : g.natDegree = f.natDegree := by
        rw [hgdef, collatzT_two_of_odd hodd, evenStep_natDegree,
            oddStep_natDegree hodd]
        omega
      by_cases hg0 : g.coeff 0 = 0
      · -- even g: one more division drops the degree strictly
        refine ⟨3, ?_⟩
        rw [Function.iterate_succ_apply', ← hgdef, collatzT_of_even hg0,
            evenStep_natDegree, hdegg]
        omega
      · rcases zmod2_cases (g.coeff 0) with h0' | h1'
        · exact absurd h0' hg0
        by_cases hg1 : g = 1
        · -- reached 1 at k = 2
          refine ⟨2, ?_⟩
          rw [← hgdef, hg1, natDegree_one]
          omega
        · -- the trailing multiplicity dropped by one: recurse
          have hstep := plateau_step_identity hodd
          have hnd : ¬ (X ^ (v + 1) ∣ (g + 1)) := by
            intro hd
            apply hdvd
            have h1 : X ^ (v + 1 + 1) ∣ X * (g + 1) := by
              obtain ⟨c, hc⟩ := hd
              exact ⟨c, by rw [hc, pow_succ]; ring⟩
            rw [← hgdef] at hstep
            rw [hstep] at h1
            exact (isCoprime_X_X_add_one.pow_left).dvd_of_dvd_mul_left h1
          obtain ⟨k', hk'⟩ := ih g h1' hg1 hnd
          refine ⟨k' + 2, ?_⟩
          rw [Function.iterate_add_apply, ← hgdef, ← hdegg]
          exact hk'

/-- **The Hicks–Mullen–Yucas–Zavislak theorem** (*Amer. Math. Monthly* 115(7), 2008):
every nonzero polynomial over `𝔽₂` reaches `1` under the Collatz map
`T(f) = f/x | (x+1)f + 1`.  Believed to be the first formalization.  The proof is
strong induction on the degree, with the plateau telescope supplying the exit. -/
theorem collatz_F2X (f : F2X) (hf : f ≠ 0) : ∃ k, collatzT^[k] f = 1 := by
  suffices h : ∀ n : ℕ, ∀ f : F2X, f ≠ 0 → f.natDegree = n →
      ∃ k, collatzT^[k] f = 1 from h f.natDegree f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hdeg
    by_cases hodd : f.coeff 0 = 0
    · -- even: divide and recurse at a smaller degree
      have hd0 : f.natDegree ≠ 0 := by
        intro h0
        have hC := eq_C_of_natDegree_eq_zero h0
        rw [hodd, C_0] at hC
        exact hf hC
      have hne' : f /ₘ X ≠ 0 := evenStep_ne_zero hf hodd
      have hdeg' := evenStep_natDegree f
      obtain ⟨k, hk⟩ := ih (n - 1) (by omega) (f /ₘ X) hne' (by omega)
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_add_apply, Function.iterate_one, collatzT_of_even hodd]
      exact hk
    · rcases zmod2_cases (f.coeff 0) with h0 | h1
      · exact absurd h0 hodd
      by_cases hone : f = 1
      · exact ⟨0, by rw [Function.iterate_zero_apply]; exact hone⟩
      · -- odd ≠ 1: plateau exit, then recurse
        have hsum : f + 1 ≠ 0 := by
          intro hsum0
          apply hone
          have h11 : (1 : F2X) + 1 = 0 := by
            rw [show (1 : F2X) = C 1 from C_1.symm, ← C_add,
                show (1 + 1 : ZMod 2) = 0 from by decide, C_0]
          calc f = f + ((1 : F2X) + 1) := by rw [h11, add_zero]
            _ = (f + 1) + 1 := by ring
            _ = 0 + 1 := by rw [hsum0]
            _ = 1 := by ring
        have hnd : ¬ (X ^ ((f + 1).natDegree + 1) ∣ (f + 1)) :=
          not_X_pow_natDegree_succ_dvd hsum
        obtain ⟨k₁, hk₁⟩ := plateau_exit (f + 1).natDegree f h1 hone hnd
        have hne₁ : collatzT^[k₁] f ≠ 0 := collatzT_iterate_ne_zero hf k₁
        obtain ⟨k₂, hk₂⟩ :=
          ih ((collatzT^[k₁] f).natDegree) (by omega) (collatzT^[k₁] f) hne₁ rfl
        refine ⟨k₂ + k₁, ?_⟩
        rw [Function.iterate_add_apply]
        exact hk₂

end CollatzLean4.F2
