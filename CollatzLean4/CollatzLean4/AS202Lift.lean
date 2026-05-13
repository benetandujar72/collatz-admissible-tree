/-
**`aS202` precision lift**.

The Lean repository defines `aS202 : Nat = 1 + 3^22 = 31381059610`,
the canonical representative of the S202 fixed point **modulo `3^24`**.
For cylinders at higher precision (`m ≥ 2`, i.e., modulus `3^(22m+2)`
with `22m + 2 ≥ 46`), this representative is **incorrect** — the true
3-adic fixed point has additional digits beyond `3^24`.

This module supplies precomputed representatives `aS202_at` for the
m-th cylinder, satisfying the **defining modular equation**
\[
  (2^{43} - 3^{22}) \cdot \mathrm{aS202\_at}(m) \equiv B_{S202} \pmod{3^{22m+2}}.
\]

For each `m`, the value is hard-coded; the proof of correctness is by
`native_decide` (pure modular arithmetic). Future cylinders are added
by extending the `match`.

**Significance**: this is the building block for `m ≥ 2` cert lifting.
The existing `aS202` is consistent with `aS202_at m` reduced
modulo `3^24`, but distinct above that precision. -/

import CollatzLean4.S202Cylinders

namespace CollatzLean4.Admissible

/-- Precomputed 3-adic representative of the S202 fixed point at
precision `3^(22m+2)`. Values for `m ≥ 4` are placeholders (return `0`)
and must be extended manually when needed. -/
def aS202_at : Nat → Nat
  | 1 => 31381059610                        -- 1 + 3^22, modulus 3^24
  | 2 => 7473280404920504074066             -- modulus 3^46
  | 3 => 33445648520278797219953204883205   -- modulus 3^68
  | _ => 0                                  -- TODO: extend

/-! ### Defining modular equation -/

/-- For `m = 1`, `aS202_at 1` satisfies the S202 fixed-point equation
mod `3^24`. -/
theorem aS202_at_1_fixed_point :
    (2^43 - 3^22) * aS202_at 1 % (3^24) = BS202 % (3^24) := by
  native_decide

/-- For `m = 2`, `aS202_at 2` satisfies the S202 fixed-point equation
mod `3^46`. -/
theorem aS202_at_2_fixed_point :
    (2^43 - 3^22) * aS202_at 2 % (3^46) = BS202 % (3^46) := by
  native_decide

/-- For `m = 3`, `aS202_at 3` satisfies the S202 fixed-point equation
mod `3^68`. -/
theorem aS202_at_3_fixed_point :
    (2^43 - 3^22) * aS202_at 3 % (3^68) = BS202 % (3^68) := by
  native_decide

/-! ### Consistency with the Lean-default `aS202` -/

/-- For `m = 1`, the precomputed representative matches the Lean-default
`aS202 = 1 + 3^22`. -/
theorem aS202_at_1_eq_aS202 : aS202_at 1 = aS202 := by native_decide

/-- For `m = 2`, the precomputed representative AGREES with `aS202`
modulo `3^24` (consistency with the lower-precision representative). -/
theorem aS202_at_2_mod_3_24 : aS202_at 2 % (3^24) = aS202 := by
  native_decide

/-- For `m = 2`, the precomputed representative DIFFERS from
`aS202 = 1 + 3^22` modulo `3^46` — capturing the higher-precision
3-adic digits that the Lean-default representation drops. -/
theorem aS202_at_2_ne_aS202_mod_3_46 :
    aS202_at 2 % (3^46) ≠ aS202 % (3^46) := by native_decide

/-- For `m = 3`, the representative AGREES with `aS202_at 2`
modulo `3^46` (coherence in the 3-adic Cauchy sequence). -/
theorem aS202_at_3_mod_3_46 : aS202_at 3 % (3^46) = aS202_at 2 := by
  native_decide

/-! ### Bound for use as `InvVertex.c`

Each representative is bounded by its modulus (canonical Nat form). -/

theorem aS202_at_1_lt_3_24 : aS202_at 1 < 3^24 := by native_decide
theorem aS202_at_2_lt_3_46 : aS202_at 2 < 3^46 := by native_decide
theorem aS202_at_3_lt_3_68 : aS202_at 3 < 3^68 := by native_decide

/-! ### Modular characterisation: `aS202_at m + 3^(22m+2) ℤ ⊆ S202` cylinder

The defining equation says `aS202_at m` is in the m-th S202 cylinder.
We restate this in the standard "≡ aS202 mod 3^(22m+2)" form used by
`S216BarrierForWords` — but with `aS202_at m` replacing the
lower-precision `aS202`. -/

/-- For m=1: the precomputed representative is IN the m=1 cylinder
(since equal to `aS202` mod `3^24`). -/
theorem aS202_at_1_in_cylinder : aS202_at 1 % (3^24) = aS202 % (3^24) := by
  native_decide

/-- For m=2: the precomputed representative is NOT in the cylinder
defined by `aS202` at precision `3^46`. The two representatives
describe DIFFERENT cylinders at precision `3^46`. -/
theorem aS202_at_2_not_in_low_precision_cylinder :
    aS202_at 2 % (3^46) ≠ aS202 % (3^46) :=
  aS202_at_2_ne_aS202_mod_3_46

/-! ### Path forward (documented)

The next refactor required to unlock `m ≥ 2` certificates:

  1. Generalise `InvStart : Nat → InvVertex` to use `aS202_at m`:
     ```
     def InvStart' (m : Nat) : InvVertex := ⟨0, aS202_at m⟩
     ```
     (replacing the current `aS202 % (3^(22m+2))` which gives the
     wrong representative for `m ≥ 2`).

  2. Generalise `S216BarrierForWords` to use `aS202_at m` in the
     cylinder constraint.

  3. Reprove `deltaPlus_aS202_general` for the new representative
     (the value `R - 22` still holds because `ν₃(aS202_at m - 1)` is
     `22` regardless of `m` — the higher-precision digits all live
     above `3^22`).

  4. Adapt the Python certificate generator to emit certs targeting
     the correct `aS202_at m` representative (the Python engine
     already computes this correctly via `pow(DEN202, -1, M)`).

With these changes, `Cert_m2_Q6_S216` and higher-m certs can be
generated and verified, unlocking the multi-block region. -/

end CollatzLean4.Admissible
