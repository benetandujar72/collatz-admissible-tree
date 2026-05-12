/-
Negative-run map  L(n) = (2n − 1) / 3  and its k-th iterate.

Key facts:
   S203-C: L^k(n) ∈ ℤ  ⇔  n ≡ −1  (mod 3^k).
   S203-D: under integrality, `3^k · L^k(n) = 2^k(n+1) − 3^k`
           (closed form matches the iterative one).
-/

import Mathlib

namespace CollatzLean4.NegativeRuns

def LInt (n : Int) : Int := (2 * n - 1) / 3

/-- Closed form numerator of L^k:  2^k n + 2^k − 3^k. -/
def Lnum (k : Nat) (n : Int) : Int :=
  (2 ^ k : Int) * n + (2 ^ k : Int) - (3 ^ k : Int)

/-- Integrality criterion for k iterations of L:
    `L^k(n) ∈ ℤ` iff `n ≡ −1 (mod 3^k)`. -/
theorem negative_run_integrality_iff (k : Nat) (n : Int) :
    ((3 ^ k : Int) ∣ Lnum k n) ↔ n ≡ -1 [ZMOD ((3 ^ k : Int))] := by
  unfold Lnum
  rw [show (2 ^ k : Int) * n + (2 ^ k : Int) - (3 ^ k : Int)
        = (2 ^ k : Int) * (n + 1) - (3 ^ k : Int) by ring]
  have hcop : IsCoprime ((3 : Int) ^ k) ((2 : Int) ^ k) := by
    have : IsCoprime (3 : Int) 2 := by decide
    exact this.pow
  have hdsub : ∀ x : Int, ((3^k : Int) ∣ x - (3^k : Int)) ↔ ((3^k : Int) ∣ x) := by
    intro x
    refine ⟨fun h => ?_, fun h => dvd_sub h (dvd_refl _)⟩
    have : (3^k : Int) ∣ (x - (3^k : Int)) + (3^k : Int) := dvd_add h (dvd_refl _)
    simpa using this
  rw [hdsub, Int.modEq_iff_dvd]
  have hneg : (-1 - n : Int) = -(n + 1) := by ring
  rw [hneg, dvd_neg]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => h.mul_left _⟩

/-- `k`-th iterate of `LInt`. -/
def Lk : Nat → Int → Int
  | 0,     n => n
  | (k+1), n => LInt (Lk k n)

@[simp] theorem Lk_zero (n : Int) : Lk 0 n = n := rfl

theorem Lk_succ (k : Nat) (n : Int) : Lk (k+1) n = LInt (Lk k n) := rfl

@[simp] theorem Lnum_zero (n : Int) : Lnum 0 n = n := by
  unfold Lnum; ring

/-- Algebraic recurrence for the numerator (no integrality needed). -/
theorem Lnum_succ (k : Nat) (n : Int) :
    Lnum (k+1) n = 2 * Lnum k n - (3 : Int) ^ k := by
  unfold Lnum
  simp only [pow_succ]
  ring

/-- S203-D: closed form for `L^k` under integrality.

If `n ≡ -1 (mod 3^k)`, every intermediate `LInt` division is exact, and
the iterative form `Lk k n` matches the closed form
`Lnum k n / 3^k`. Equivalently: `3^k · Lk k n = Lnum k n`. -/
theorem Lnum_eq_three_pow_mul_Lk (k : Nat) (n : Int)
    (h : n ≡ -1 [ZMOD ((3 ^ k : Int))]) :
    Lnum k n = (3 : Int) ^ k * Lk k n := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hdvd_pow : ((3 : Int) ^ k) ∣ ((3 : Int) ^ (k+1)) :=
      ⟨3, by rw [pow_succ]⟩
    have h' : n ≡ -1 [ZMOD ((3 : Int) ^ k)] := by
      rw [Int.modEq_iff_dvd] at h ⊢
      exact dvd_trans hdvd_pow h
    have hih := ih h'
    have hdvd_full : ((3 : Int) ^ (k+1)) ∣ Lnum (k+1) n :=
      (negative_run_integrality_iff (k+1) n).mpr h
    have hrec : Lnum (k+1) n = 2 * Lnum k n - (3 : Int) ^ k :=
      Lnum_succ k n
    have hsub : Lnum (k+1) n = (3 : Int) ^ k * (2 * Lk k n - 1) := by
      rw [hrec, hih]; ring
    -- From 3^(k+1) ∣ 3^k · (2·Lk k n − 1), cancel 3^k to get 3 ∣ 2·Lk k n − 1.
    have hdvd_three : (3 : Int) ∣ 2 * Lk k n - 1 := by
      rw [hsub] at hdvd_full
      obtain ⟨m, hm⟩ := hdvd_full
      have hpow_ne : ((3 : Int) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hsplit :
          (3 : Int) ^ k * (2 * Lk k n - 1) = (3 : Int) ^ k * (3 * m) := by
        rw [hm, pow_succ]; ring
      exact ⟨m, mul_left_cancel₀ hpow_ne hsplit⟩
    obtain ⟨m, hm⟩ := hdvd_three
    rw [hsub, Lk_succ]
    unfold LInt
    rw [hm, pow_succ]
    have hdivm : (3 * m : Int) / 3 = m := by omega
    rw [hdivm]; ring

end CollatzLean4.NegativeRuns
