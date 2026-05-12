/-
S206 — low-slope periodic block: 3-adic fixed point check for w = wS202.

  A = 43, q = 22, B = 919447060349,
  a_w ≡ 31381059610  (mod 3^24),
  (2^43 − 3^22) · a_w ≡ B   (mod 3^24).

Also: starting wS202 from 251 does NOT reproduce the same (A,q) balance,
so the 3-adic fixed point is not accessed directly from 1 by this block.
-/

import CollatzLean4.Defect
import Mathlib.Data.ZMod.Basic

namespace CollatzLean4.Admissible

-- AS202, qS202, BS202 are defined in `CollatzLean4.Defect`.
def aS202 : Nat := 31381059610

/-- 3-adic fixed-point identity mod `3^24` (verified by `native_decide`). -/
theorem S206_fixed_point_mod :
    ((2 : ZMod (3 ^ 24)) ^ 43 - (3 : ZMod (3 ^ 24)) ^ 22) *
      (aS202 : ZMod (3 ^ 24))
    = (BS202 : ZMod (3 ^ 24)) := by
  native_decide

theorem S206_a_mod9 : aS202 % 9 = 1 := by native_decide

/-- Replaying `wS202` from n = 251 keeps q = 22… -/
theorem S206_repeat_from_251_q : (evalWordFrom 251 wS202).q = 22 := by
  native_decide

/-- …but A is 68 (not 60 as in the spec, nor 43 as in the central run). -/
theorem S206_repeat_from_251_A : (evalWordFrom 251 wS202).A = 68 := by
  native_decide

theorem S206_not_direct_repeat_low_slope :
    (evalWordFrom 251 wS202).A ≠ 43 := by native_decide

end CollatzLean4.Admissible
