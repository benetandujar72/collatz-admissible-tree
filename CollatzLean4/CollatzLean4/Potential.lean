/-
S214 — Computable 3-adic potential functions (`ν₃`, `ρ+`, `ρ-`, `δ+`)
and the S214 mixed-potential template.

Following the S212–S220 program: this module supplies the analytic
"ingredients" of the local 3-adic potential framework, making them
available as Lean `def`s suitable for use as the candidate Φ in a
`LocalPotentialCertificate`.

CONTENT:

  * `nu3 n c` — 3-adic valuation of `n`, capped at `c`.
  * `rhoPlus`, `rhoMinus`, `deltaPlus` — distance functions to `1` /
    proximity to `−1` in the 3-adic cylinder.
  * `s214Potential λ γ μ Q h ψ` — the S214 mixed potential template.
  * Specific verification: `deltaPlus aS202 24 = 2`,
    `deltaPlus aS202 46 = 24` — the ladder structure for `m = 1, 2`.

S215 / S219 NOTES:

  * S215 over-cover warning: any abstraction using only `c mod 3^h`
    with `h ≤ 22` confuses `aS202` with `1` (since `aS202 ≡ 1
    (mod 3^22)` from `aS202_sub_one`). The lemma `aS202_ne_one_mod_3_pow_23`
    below verifies that this confusion *disappears* at `h = 23`.

  * S219 mode requirement: the `LiftedCertificate` interface in
    `PathWordCorrespondence.lean` requires the dist table to satisfy
    the Bellman-Ford relaxation invariant for *every* generated edge.
    This is the "certified mode" requirement. Heuristically-pruned
    "scout-mode" data does NOT satisfy this and cannot be lifted.
-/

import CollatzLean4.S202Cylinders
import CollatzLean4.InverseGraph

namespace CollatzLean4.Admissible

/-! ### `ν₃` 3-adic valuation -/

/-- 3-adic valuation of `n`, capped at `c`. Returns `0` if `n = 0` or
no factor of 3, otherwise the largest `k ≤ c` with `3^k ∣ n`. -/
def nu3 (n : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 =>
      if n = 0 then 0
      else if n % 3 = 0 then 1 + nu3 (n / 3) c
      else 0

@[simp] theorem nu3_zero_cap (n : Nat) : nu3 n 0 = 0 := by
  cases n <;> rfl

theorem nu3_le_cap (n c : Nat) : nu3 n c ≤ c := by
  induction c generalizing n with
  | zero => simp
  | succ c ih =>
      unfold nu3
      split_ifs
      · omega
      · have := ih (n / 3); omega
      · omega

/-- **ν₃ ladder**: for `cap ≥ k`, the capped 3-adic valuation of `3^k`
equals exactly `k`. The base case `k = 0` returns `0` (since `1 % 3 ≠ 0`),
and each successive `3^k = 3 · 3^(k−1)` contributes one to the count. -/
theorem nu3_three_pow (k cap : Nat) (h : k ≤ cap) : nu3 (3 ^ k) cap = k := by
  induction k generalizing cap with
  | zero =>
      -- 3 ^ 0 = 1; nu3 1 cap = 0 since 1 % 3 = 1 ≠ 0.
      cases cap with
      | zero => simp [nu3]
      | succ c =>
          show nu3 1 (c + 1) = 0
          unfold nu3
          simp
  | succ k ih =>
      cases cap with
      | zero => omega
      | succ c =>
          have h_pos : (3 : Nat) ^ (k + 1) ≠ 0 := by positivity
          have h_div3 : (3 : Nat) ^ (k + 1) % 3 = 0 := by
            rw [pow_succ]; exact Nat.mul_mod_left _ _
          have h_quot : (3 : Nat) ^ (k + 1) / 3 = 3 ^ k := by
            rw [pow_succ]; exact Nat.mul_div_cancel _ (by decide : 0 < 3)
          unfold nu3
          rw [if_neg h_pos, if_pos h_div3, h_quot]
          have hkc : k ≤ c := by omega
          rw [ih c hkc]
          omega

/-! ### Distance functions -/

/-- `ρ_+(c, r)`: 3-adic proximity to `1`, capped at `r`. Returns `r`
when `c = 1` (max proximity = cap). -/
def rhoPlus (c r : Nat) : Nat :=
  if c = 1 then r else nu3 (c - 1) r

/-- `ρ_-(c, r)`: 3-adic proximity to `−1`, capped at `r`. Computed
as `nu3 (c + 1) r`. -/
def rhoMinus (c r : Nat) : Nat :=
  nu3 (c + 1) r

/-- `δ_+(c, r) = r − ρ_+(c, r)`: 3-adic distance to `1`. -/
def deltaPlus (c r : Nat) : Nat := r - rhoPlus c r

/-! ### Concrete S202 ladder values

For `m = 1, 2`, `δ_+(aS202, R_m) = 22m − 20` matches the analytical
prediction from the S214 paper. Both verified by `native_decide`. -/

theorem deltaPlus_aS202_m1 : deltaPlus aS202 24 = 2 := by native_decide

theorem deltaPlus_aS202_m2 : deltaPlus aS202 46 = 24 := by native_decide

theorem deltaPlus_aS202_m3 : deltaPlus aS202 68 = 46 := by native_decide

/-- **S214 δ₊ ladder, general form**: for every `m ≥ 1`, the 3-adic
distance from `aS202` to `1` at base precision `R_m = 22m + 2` equals
`22m − 20`. Follows from `aS202 − 1 = 3^22` (i.e., `ν₃(aS202 − 1) = 22`)
and `nu3_three_pow`. -/
theorem deltaPlus_aS202_general (m : Nat) (hm : 1 ≤ m) :
    deltaPlus aS202 (22 * m + 2) = 22 * m - 20 := by
  unfold deltaPlus rhoPlus
  rw [if_neg (by decide : aS202 ≠ 1), aS202_sub_one,
      nu3_three_pow 22 (22 * m + 2) (by omega)]
  omega

/-! ### S215 over-cover warning: `aS202` distinguished from `1` only at `h ≥ 23` -/

/-- For all `h ≤ 22`: `aS202 ≡ 1 (mod 3^h)`. (From `aS202_mod_pow_eq_one`,
together with the `h = 0` case.) This means any abstraction collapsing
states by `c mod 3^h` with `h ≤ 22` cannot distinguish `aS202` from
the root `1`. -/
theorem aS202_eq_one_mod_3_pow_22 : aS202 % (3 ^ 22) = 1 % (3 ^ 22) := by
  rw [aS202_decomp]
  simp [pow_succ]

/-- **S215 distinguishing threshold**: at `h = 23`, `aS202` is no longer
`≡ 1`. Hence abstractions for the S202 cylinder must use `h ≥ 23` to
avoid the over-cover confusion. -/
theorem aS202_ne_one_mod_3_pow_23 : aS202 % (3 ^ 23) ≠ 1 % (3 ^ 23) := by
  rw [aS202_decomp]
  -- aS202 = 1 + 3^22, mod 3^23 = 1 + 3^22 (since 1 + 3^22 < 3^23)
  -- 1 mod 3^23 = 1
  -- They differ since 3^22 ≠ 0 (mod 3^23)
  native_decide

/-! ### S214 mixed-potential template

The S214 paper proposes potentials of the form:

  Φ(j, c) = λ · δ_+(c, R+j) + γ · ρ_-(c, R+j) − μ · (Q − j)
           + ψ(c mod 3^h)

This is a candidate Φ; whether it satisfies the
`LocalPotentialCertificate` edge condition for the S202 inverse graph
is the S214 conjecture (open). -/

/-- Candidate S214 potential. Parameters:
  * `R` : base cylinder precision (`22m + 2`).
  * `Q` : zero-budget.
  * `h` : local-correction modular depth (must satisfy `h ≥ 23` for
    S202; see `aS202_ne_one_mod_3_pow_23`).
  * `lam, gam, mu : Int` : weights of the three structural terms.
  * `psi : Nat → Int` : finite local correction table indexed by
    `c mod 3^h`. -/
def s214Potential (R Q h : Nat) (lam gam mu : Int)
    (psi : Nat → Int) (v : InvVertex) : Int :=
  lam * (deltaPlus v.c (R + v.j) : Int)
    + gam * (rhoMinus v.c (R + v.j) : Int)
    - mu * ((Q : Int) - (v.j : Int))
    + psi (v.c % 3 ^ h)

/-! ### Sanity: `s214Potential` evaluates -/

/-- A trivial sanity check: with `λ = γ = μ = 0` and `ψ ≡ 0`, the
potential is identically zero. -/
theorem s214Potential_zero (R Q h : Nat) (v : InvVertex) :
    s214Potential R Q h 0 0 0 (fun _ => 0) v = 0 := by
  unfold s214Potential
  ring

end CollatzLean4.Admissible
