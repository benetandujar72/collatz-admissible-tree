/-
**3-adic ρ₊ transition laws for inverse-cylinder edges.**

Formal down-payment on the discrete-log / lifting-the-exponent attack vector
(see the `structure_probe.py` verification: the laws hold with 0 violations).
This file formalises:

  * `nu3_mul_three` — `ν₃(3·x) = ν₃(x) + 1` (capped), a reusable building block
    for the τ=2 "climb" law.
  * `zeroEdge_tau_3_deltaPlus_max` — the τ=3 zero-edge **reset** law: the target
    saturates `δ₊ = R + j` (i.e. ρ₊ = 0), the τ=3 analogue of the existing τ=1
    `zeroEdge_tau_1_deltaPlus_max`. Together with τ=1 this confirms that
    **odd-τ zero-edges reset the root-proximity ρ₊** — one half of the verified
    transition table.

The τ=2 "climb" law (`ρ₊(c') = ρ₊(c)+1`) and the one-edge discrete-log law
(`ρ₊(c') = ν₃(c − 2^τ)`) are the remaining (harder) laws: both need a
`ν₃(unit · x) = ν₃(x)` lemma for the project's custom `nu3`, scoped as the next
step.
-/

import CollatzLean4.TrivialPotential

namespace CollatzLean4.Admissible

/-- **`ν₃(3·x) = ν₃(x) + 1`** (capped), for `x ≠ 0`. Near-definitional: at cap
`c+1`, `3·x` is nonzero and divisible by 3 with quotient `x`. Building block for
the τ=2 climb law. -/
theorem nu3_mul_three (x c : Nat) (hx : x ≠ 0) :
    nu3 (3 * x) (c + 1) = nu3 x c + 1 := by
  have h_div : (3 * x) / 3 = x := Nat.mul_div_cancel_left x (by decide)
  show (if 3 * x = 0 then 0
        else if (3 * x) % 3 = 0 then 1 + nu3 (3 * x / 3) c else 0) = nu3 x c + 1
  rw [if_neg (by positivity), if_pos (Nat.mul_mod_right 3 x), h_div, Nat.add_comm]

/-- **τ=3 zero-edge residue law**: a `τ(c') = 3` inverse-zero-edge forces
`c' ≡ 2 (mod 3)`. (Same conclusion as the τ=1 case: `2^τ ≡ 2 (mod 3)` for odd
`τ`, so the forward-consistency congruence pins `c' mod 3`.) -/
theorem zeroEdge_tau_3_vc_mod3
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_3 : tau v'.c = 3) :
    v'.c % 3 = 2 := by
  obtain ⟨_h_j_eq, _h_X, h_consistency, _h_ω⟩ := h_zero
  rw [h_tau_3] at h_consistency
  have h_pow : (2 : Nat) ^ 3 = 8 := by norm_num
  rw [h_pow] at h_consistency
  have h_3_dvd : (3 : Nat) ∣ 3 ^ (R + v'.j) :=
    dvd_pow_self 3 (by omega : R + v'.j ≠ 0)
  have hL := Nat.mod_mod_of_dvd (3 * v.c + 1) h_3_dvd
  have hRr := Nat.mod_mod_of_dvd (8 * v'.c) h_3_dvd
  have h_mod3 : (3 * v.c + 1) % 3 = (8 * v'.c) % 3 := by
    rw [← hL, h_consistency, hRr]
  omega

/-- **Saturated target potential for τ=3 zero-edges**: like the τ=1 case, the
root-distance reaches its cap, `δ₊(c', R+j') = R+j'` (i.e. ρ₊ resets to `0`).
This is the τ=3 reset law of the verified transition table. -/
theorem zeroEdge_tau_3_deltaPlus_max
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_3 : tau v'.c = 3) :
    deltaPlus v'.c (R + v'.j) = R + v'.j := by
  have h_mod3 := zeroEdge_tau_3_vc_mod3 hR h_zero h_tau_3
  have h_vc_ne_1 : v'.c ≠ 1 := by intro h; rw [h] at h_mod3; omega
  have h_vc_sub_mod3 : (v'.c - 1) % 3 ≠ 0 := by
    have : (v'.c - 1) % 3 = 1 := by omega
    omega
  unfold deltaPlus rhoPlus
  rw [if_neg h_vc_ne_1,
      nu3_eq_zero_of_mod_three_ne_zero (v'.c - 1) (R + v'.j) h_vc_sub_mod3]
  omega

end CollatzLean4.Admissible
