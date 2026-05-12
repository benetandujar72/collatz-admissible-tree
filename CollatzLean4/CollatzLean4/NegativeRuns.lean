/-
Negative-run map  L(n) = (2n − 1) / 3  and its k-th iterate.

Key fact (S203-C):
   L^k(n) ∈ ℤ  ⇔  n ≡ −1  (mod 3^k).
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

end CollatzLean4.NegativeRuns
