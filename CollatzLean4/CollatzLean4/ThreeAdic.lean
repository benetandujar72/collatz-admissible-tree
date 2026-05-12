/-
3-adic lift of the S206 fixed-point identity.

S206 gives `(2^43 − 3^22) · a_{S202} ≡ B_{S202} (mod 3^24)` for one
specific `a_{S202}`. This module lifts the existence statement to all
moduli `3^k`:

  ∀ k, ∃ a : ZMod (3^k), (2^43 − 3^22) · a = B_{S202}

This is the first step toward defining the 3-adic fixed point
`a_w ∈ ℤ_3` of the cylinder `wS202`: the sequence (a_k)_{k ≥ 0} forms
a coherent system under reduction `ZMod (3^{k+1}) → ZMod (3^k)`,
hence a Cauchy sequence in ℤ_3.

The key fact is that `2^43 − 3^22` is coprime to 3 (its mod-3 image is
`2^43 mod 3 = 2`, with `3^22 ≡ 0 mod 3`), so it is a unit in every
`ZMod (3^k)`.

NOTE: this does NOT prove anything new about Collatz. It is a structural
lift, providing a clean abstract `∃` statement at every modulus where
the original `native_decide` proof only handled one specific modulus.
-/

import CollatzLean4.PeriodicBlocks
import Mathlib.Data.ZMod.Basic

namespace CollatzLean4.Admissible

/-- The shift element `2^43 − 3^22` appearing in the S206 identity. -/
def s202_shift : Nat := 2 ^ 43 - 3 ^ 22

theorem s202_shift_value : s202_shift = 8764711962599 := by
  unfold s202_shift; native_decide

theorem s202_shift_coprime_three : Nat.Coprime s202_shift 3 := by
  unfold s202_shift Nat.Coprime; native_decide

theorem s202_shift_coprime_three_pow (k : Nat) :
    Nat.Coprime s202_shift (3 ^ k) :=
  s202_shift_coprime_three.pow_right k

/-- The shift element is a unit in `ZMod (3^k)` for every `k`. -/
theorem s202_shift_isUnit (k : Nat) :
    IsUnit ((s202_shift : ZMod (3 ^ k))) := by
  rw [ZMod.isUnit_iff_coprime]
  exact s202_shift_coprime_three_pow k

/-- **S206 lifted to all moduli**: for every `k`, there exists
`a_k : ZMod (3^k)` satisfying `(2^43 − 3^22) · a_k ≡ B_{S202} (mod 3^k)`.
The sequence `(a_k)` is the start of the 3-adic Cauchy approximation
to the fixed point. -/
theorem S206_fixed_point_mod_general (k : Nat) :
    ∃ a : ZMod (3 ^ k),
      ((s202_shift : ZMod (3 ^ k))) * a = (BS202 : ZMod (3 ^ k)) := by
  obtain ⟨u, hu⟩ := s202_shift_isUnit k
  refine ⟨((u⁻¹ : (ZMod (3 ^ k))ˣ) : ZMod (3 ^ k)) * (BS202 : ZMod (3 ^ k)), ?_⟩
  calc ((s202_shift : ZMod (3 ^ k)))
        * (((u⁻¹ : (ZMod (3 ^ k))ˣ) : ZMod (3 ^ k)) * (BS202 : ZMod (3 ^ k)))
      = ((u : ZMod (3 ^ k))
          * ((u⁻¹ : (ZMod (3 ^ k))ˣ) : ZMod (3 ^ k)))
          * (BS202 : ZMod (3 ^ k)) := by rw [← hu]; ring
    _ = 1 * (BS202 : ZMod (3 ^ k)) := by rw [Units.mul_inv]
    _ = (BS202 : ZMod (3 ^ k)) := one_mul _

/-- Restatement in the original `(2^A − 3^q)` form (instead of `s202_shift`).
Equivalent to `S206_fixed_point_mod_general` via the cast
`(s202_shift : ZMod (3^k)) = (2 : ZMod (3^k))^43 − (3 : ZMod (3^k))^22`. -/
theorem S206_fixed_point_mod_general' (k : Nat) :
    ∃ a : ZMod (3 ^ k),
      ((2 : ZMod (3 ^ k)) ^ 43 - (3 : ZMod (3 ^ k)) ^ 22) * a
        = (BS202 : ZMod (3 ^ k)) := by
  have hcast :
      (2 : ZMod (3 ^ k)) ^ 43 - (3 : ZMod (3 ^ k)) ^ 22
        = ((s202_shift : Nat) : ZMod (3 ^ k)) := by
    unfold s202_shift
    have h_le : (3 : Nat) ^ 22 ≤ 2 ^ 43 := by norm_num
    rw [Nat.cast_sub h_le]
    push_cast
    ring
  rw [hcast]
  exact S206_fixed_point_mod_general k

end CollatzLean4.Admissible
