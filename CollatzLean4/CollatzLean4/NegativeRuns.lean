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

/-- Integrality criterion for k iterations of L. Proof reserved. -/
theorem negative_run_integrality_iff (k : Nat) (n : Int) :
    ((3 ^ k : Int) ∣ Lnum k n) ↔ n ≡ -1 [ZMOD ((3 ^ k : Int))] := by
  sorry

end CollatzLean4.NegativeRuns
