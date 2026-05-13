/-
S213 — Cylinder stability for admissible steps.

This module formalizes the key lemma underlying S209/S210: the
τ-trajectory of an admissible word `w` depends only on the cylinder
class of the starting state, provided the cylinder is deep enough
to absorb the precision losses from `zero` steps.

KEY INSIGHTS:

  * `τ` depends only on `n mod 9` (from `tau_mod`).
  * `9 = 3²`, so any cylinder `3^k` with `k ≥ 2` determines `n mod 9`.
  * `Branch.one` preserves cylinder precision exactly.
  * `Branch.zero` loses one 3-adic digit (divides by 3).
  * After a word with `q` zeros, cylinder precision drops by `q`.

If the starting cylinder has precision `22m + 2` and the word `wS202`
has 22 zeros, then after the word we still have precision 2 (i.e.,
mod 9), exactly enough for the next iteration's `τ` to match.

CONTENT:

  * `step_one_cong` — `Branch.one` preserves the cylinder (full proof).
  * `step_zero_cong` — `Branch.zero` loses one digit (full proof).
  * `runWord_cong` — composition: precision drops by `q(w)`.

DOWNSTREAM (not in this module):

  * Specialize to `wS202`: precision `22m + 2` survives `wS202^m`.
  * Conclude `defectChange wS202` is uniform on the cylinder.
  * Discharge the `h_uniform` hypothesis in `S211_S202_subcritical`.
-/

import CollatzLean4.AdmissibleBasic

namespace CollatzLean4.Admissible

/-! ### Cylinder predicate -/

/-- Two states are in the same `3^k` cylinder if their `n` values agree
modulo `3^k`. -/
def InSameCylinder (s s' : AdmState) (k : Nat) : Prop :=
  s.n ≡ s'.n [MOD 3 ^ k]

theorem inSameCylinder_refl (s : AdmState) (k : Nat) :
    InSameCylinder s s k := Nat.ModEq.refl _

theorem inSameCylinder_symm {s s' : AdmState} {k : Nat}
    (h : InSameCylinder s s' k) : InSameCylinder s' s k :=
  Nat.ModEq.symm h

/-! ### `τ` stability inside a cylinder -/

/-- For `k ≥ 2`, states in the same cylinder share their `n mod 9`. -/
theorem mod_nine_of_cylinder {s s' : AdmState} {k : Nat} (hk : k ≥ 2)
    (h : InSameCylinder s s' k) : s.n ≡ s'.n [MOD 9] := by
  have hdvd : (9 : Nat) ∣ 3 ^ k := by
    have h9 : (9 : Nat) = 3 ^ 2 := by norm_num
    rw [h9]
    exact pow_dvd_pow 3 hk
  exact h.of_dvd hdvd

/-- For `k ≥ 2`, states in the same cylinder share their τ value. -/
theorem tau_eq_of_cylinder {s s' : AdmState} {k : Nat} (hk : k ≥ 2)
    (h : InSameCylinder s s' k) : tau s.n = tau s'.n := by
  have h9 : s.n ≡ s'.n [MOD 9] := mod_nine_of_cylinder hk h
  rw [tau_mod s.n, tau_mod s'.n]
  exact congrArg tau h9

/-! ### `Branch.one` preserves the cylinder -/

/-- `step s Branch.one` and `step s' Branch.one` stay in the same cylinder
when their inputs do (and `k ≥ 2`). -/
theorem step_one_cong {s s' : AdmState} {k : Nat} (hk : k ≥ 2)
    (h : InSameCylinder s s' k) :
    InSameCylinder (step s Branch.one) (step s' Branch.one) k := by
  have h_tau : tau s.n = tau s'.n := tau_eq_of_cylinder hk h
  show (2 ^ tau s.n * s.n) ≡ (2 ^ tau s'.n * s'.n) [MOD 3 ^ k]
  rw [h_tau]
  exact h.mul_left _

/-! ### `Branch.zero` loses one digit of precision

`Branch.zero` divides by 3, so the cylinder precision drops by 1.
-/

/-- Auxiliary: if `3 ∣ a`, `3 ∣ b`, and `a ≡ b (mod 3·m)` with `m ≥ 1`,
then `a/3 ≡ b/3 (mod m)`. -/
private lemma div_three_modEq_of_dvd {a b m : Nat} (_hm : 1 ≤ m)
    (ha : 3 ∣ a) (hb : 3 ∣ b) (h : a ≡ b [MOD 3 * m]) :
    (a / 3) ≡ (b / 3) [MOD m] := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  rw [Nat.mul_div_cancel_left a' (by norm_num : (0 : Nat) < 3),
      Nat.mul_div_cancel_left b' (by norm_num : (0 : Nat) < 3)]
  unfold Nat.ModEq at h ⊢
  have key1 : (3 * a') % (3 * m) = 3 * (a' % m) := Nat.mul_mod_mul_left _ _ _
  have key2 : (3 * b') % (3 * m) = 3 * (b' % m) := Nat.mul_mod_mul_left _ _ _
  rw [key1, key2] at h
  omega

/-- Auxiliary: from `a ≡ b [MOD n]` with `a, b ≥ 1`, derive
`a − 1 ≡ b − 1 [MOD n]` (Nat truncated subtraction). -/
private lemma sub_one_modEq_of_pos {a b n : Nat}
    (h : a ≡ b [MOD n]) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a - 1) ≡ (b - 1) [MOD n] := by
  have ea : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
  have eb : b = (b - 1) + 1 := (Nat.sub_add_cancel hb).symm
  rw [ea, eb] at h
  exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) h

/-- `step s Branch.zero` and `step s' Branch.zero` stay in a slightly
smaller cylinder when their inputs are in a `3^k` cylinder
(precision drops by 1 due to division by 3). Requires `k ≥ 2` and
both states are `InX`. -/
theorem step_zero_cong {s s' : AdmState} {k : Nat} (hk : k ≥ 2)
    (h_inX_s : InX s.n) (h_inX_s' : InX s'.n)
    (h : InSameCylinder s s' k) :
    InSameCylinder (step s Branch.zero) (step s' Branch.zero) (k - 1) := by
  have h_tau : tau s.n = tau s'.n := tau_eq_of_cylinder hk h
  have h_div_s : 3 ∣ (2 ^ tau s.n * s.n - 1) := psiZero_integrality h_inX_s
  have h_div_s' : 3 ∣ (2 ^ tau s'.n * s'.n - 1) := psiZero_integrality h_inX_s'
  -- Numerators are congruent mod 3^k:
  have h_num : (2 ^ tau s.n * s.n - 1) ≡ (2 ^ tau s'.n * s'.n - 1)
                  [MOD 3 ^ k] := by
    have hmul : (2 ^ tau s.n * s.n) ≡ (2 ^ tau s'.n * s'.n) [MOD 3 ^ k] := by
      have hm := h.mul_left (2 ^ tau s'.n)
      rw [h_tau]; exact hm
    have hpos_s : 1 ≤ 2 ^ tau s.n * s.n := by
      have := psiZero_mul_mod h_inX_s; omega
    have hpos_s' : 1 ≤ 2 ^ tau s'.n * s'.n := by
      have := psiZero_mul_mod h_inX_s'; omega
    exact sub_one_modEq_of_pos hmul hpos_s hpos_s'
  -- Rewrite 3^k = 3 * 3^(k-1) and apply div_three_modEq_of_dvd.
  have hpow : 3 ^ k = 3 * 3 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
    conv_lhs => rw [hk1]
    rw [pow_succ]; ring
  rw [hpow] at h_num
  show ((2 ^ tau s.n * s.n - 1) / 3) ≡ ((2 ^ tau s'.n * s'.n - 1) / 3)
        [MOD 3 ^ (k - 1)]
  have hm1 : 1 ≤ 3 ^ (k - 1) := Nat.one_le_pow _ _ (by norm_num)
  exact div_three_modEq_of_dvd hm1 h_div_s h_div_s' h_num

/-! ### Composing over a word: `runWord_cong`

For a word `w` with `q(w)` zeros, running it from two cylinder-equivalent
states produces results in a cylinder whose precision is `k - q(w)`.
This is the formal statement of S213: cylinder propagation through an
admissible word loses exactly one 3-adic digit per `zero` step. -/

/-- Number of `Branch.zero` symbols in a word. -/
def Word.numZeros : Word → Nat
  | []                  => 0
  | Branch.zero :: bs   => Word.numZeros bs + 1
  | Branch.one  :: bs   => Word.numZeros bs

@[simp] theorem Word.numZeros_nil : Word.numZeros [] = 0 := rfl

@[simp] theorem Word.numZeros_cons_zero (bs : Word) :
    Word.numZeros (Branch.zero :: bs) = Word.numZeros bs + 1 := rfl

@[simp] theorem Word.numZeros_cons_one (bs : Word) :
    Word.numZeros (Branch.one :: bs) = Word.numZeros bs := rfl

/-- Number of `Branch.one` symbols in a word. -/
def Word.numOnes : Word → Nat
  | []                  => 0
  | Branch.zero :: bs   => Word.numOnes bs
  | Branch.one  :: bs   => Word.numOnes bs + 1

@[simp] theorem Word.numOnes_nil : Word.numOnes [] = 0 := rfl

@[simp] theorem Word.numOnes_cons_zero (bs : Word) :
    Word.numOnes (Branch.zero :: bs) = Word.numOnes bs := rfl

@[simp] theorem Word.numOnes_cons_one (bs : Word) :
    Word.numOnes (Branch.one :: bs) = Word.numOnes bs + 1 := rfl

/-- The total word length equals the sum of `numOnes` and `numZeros`. -/
theorem Word.length_eq_numOnes_add_numZeros (u : Word) :
    u.length = Word.numOnes u + Word.numZeros u := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
      cases b
      · simp [Word.numOnes_cons_one, Word.numZeros_cons_one, ih, List.length_cons]
        omega
      · simp [Word.numOnes_cons_zero, Word.numZeros_cons_zero, ih, List.length_cons]
        omega

/-- S213 main theorem: cylinder propagation through an admissible word.
Starting from cylinder precision `k ≥ numZeros w + 2` ensures the
result is in a cylinder of precision `k - numZeros w ≥ 2`. -/
theorem runWord_cong (w : Word) {s s' : AdmState} {k : Nat}
    (hk : k ≥ Word.numZeros w + 2)
    (h_inv_s : Inv s) (h_inv_s' : Inv s')
    (h : InSameCylinder s s' k) :
    InSameCylinder (runWord w s) (runWord w s') (k - Word.numZeros w) := by
  induction w generalizing s s' k with
  | nil =>
      simp [runWord]
      exact h
  | cons b bs ih =>
      cases b with
      | one =>
          have h_step : InSameCylinder (step s Branch.one) (step s' Branch.one) k :=
            step_one_cong (by omega) h
          show InSameCylinder (runWord bs (step s Branch.one))
                (runWord bs (step s' Branch.one))
                (k - Word.numZeros (Branch.one :: bs))
          rw [Word.numZeros_cons_one]
          apply ih
          · simp [Word.numZeros] at hk; exact hk
          · exact step_inv h_inv_s Branch.one
          · exact step_inv h_inv_s' Branch.one
          · exact h_step
      | zero =>
          have h_step :
              InSameCylinder (step s Branch.zero) (step s' Branch.zero) (k - 1) :=
            step_zero_cong (by omega) h_inv_s.2 h_inv_s'.2 h
          show InSameCylinder (runWord bs (step s Branch.zero))
                (runWord bs (step s' Branch.zero))
                (k - Word.numZeros (Branch.zero :: bs))
          have heq : k - Word.numZeros (Branch.zero :: bs)
                    = (k - 1) - Word.numZeros bs := by
            simp [Word.numZeros]; omega
          rw [heq]
          apply ih
          · simp [Word.numZeros] at hk; omega
          · exact step_inv h_inv_s Branch.zero
          · exact step_inv h_inv_s' Branch.zero
          · exact h_step

end CollatzLean4.Admissible
