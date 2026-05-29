/-
**Lifting-the-exponent (LTE) bound for `ν₃(2^S − 1)`.**

This module derives the CORRECT closed form for the 3-adic valuation of
`2^S − 1`, the key analytic ingredient behind the τ=2 climb / discrete-log
law on the S202 slope-barrier sub-route.

The naive guess `ν₃(2^S − 1) = ν₃(S)` is WRONG. Because `3 ∤ (2 − 1) = 1`,
Mathlib's odd-prime LTE lemma `padicValNat.pow_sub_pow` cannot be applied to
the base `2` directly. We reindex through `2^{2t} = 4^t` (so that
`3 ∣ 4 − 1 = 3`) and split on the parity of the exponent:

  * `padicValNat 3 (4 ^ t − 1) = 1 + padicValNat 3 t`           (LTE, `t ≥ 1`)
  * `padicValNat 3 (2 ^ S − 1) = 0`                              (`S` odd)
  * `padicValNat 3 (2 ^ S − 1) = if Even S then 1 + padicValNat 3 S else 0`

All over Mathlib's UNcapped `padicValNat 3`, which is what `pow_sub_pow`
speaks about.

We additionally prove the bridge `nu3_eq_padicValNat_of_lt`, identifying the
project's capped `nu3` with `padicValNat 3` in the cap-not-binding regime
(`padicValNat 3 n < c`). This transports the LTE results to the existing
`rhoPlus` / `deltaPlus` machinery whenever the cap is slack.

HONEST SCOPE: these are structural facts about the 3-adic valuation feeding the
S202 *slope*-barrier half. They are NOT a proof of Collatz, nor of the full
S202 alternative (which also needs the subcritical-access branch and the
external Bandújar reduction).
-/

import CollatzLean4.Potential
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace CollatzLean4.Admissible

open scoped Classical

/-! ### Lifting-the-exponent for base 4 (so `3 ∣ 4 − 1`) -/

/-- **LTE corollary, base 4.** For `t ≥ 1`,
`ν₃(4^t − 1) = 1 + ν₃(t)`.

This is the direct application of the odd-prime lifting-the-exponent lemma
`padicValNat.pow_sub_pow` with `p = 3`, `x = 4`, `y = 1`, `n = t`. The side
conditions `Odd 3`, `1 < 4`, `3 ∣ 4 − 1`, `¬ 3 ∣ 4` all discharge by
`decide`/`norm_num`, and `ν₃(4 − 1) = ν₃ 3 = 1`. The `Fact (Nat.Prime 3)`
instance is found automatically (`Nat.fact_prime_three`). -/
theorem padicValNat_four_pow_sub_one (t : ℕ) (ht : t ≠ 0) :
    padicValNat 3 (4 ^ t - 1) = 1 + padicValNat 3 t := by
  have h :=
    padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
      (by decide)        -- hp1 : Odd 3
      (by norm_num)      -- hyx : 1 < 4
      (by decide)        -- hxy : 3 ∣ 4 - 1
      (by decide)        -- hx  : ¬ 3 ∣ 4
      ht                 -- hn  : t ≠ 0
  -- h : padicValNat 3 (4 ^ t - 1 ^ t) = padicValNat 3 (4 - 1) + padicValNat 3 t
  simpa using h

/-! ### Base-2 reformulation: even exponents -/

/-- **LTE corollary, base 2, even exponent.** For `t ≥ 1`,
`ν₃(2^{2t} − 1) = 1 + ν₃(t)`. Obtained from the base-4 statement via
`2^{2t} = 4^t`. -/
theorem padicValNat_two_pow_sub_one_even (t : ℕ) (ht : t ≠ 0) :
    padicValNat 3 (2 ^ (2 * t) - 1) = 1 + padicValNat 3 t := by
  have e : (2 : ℕ) ^ (2 * t) = 4 ^ t := by
    rw [pow_mul]; norm_num
  rw [e]; exact padicValNat_four_pow_sub_one t ht

/-! ### Base-2: odd exponents -/

/-- For odd `S`, `2^S ≡ 2 (mod 3)`, hence `3 ∤ (2^S − 1)` and
`ν₃(2^S − 1) = 0`. The congruence is proved by `Nat.pow_mod`:
`2^S % 3 = 2^(S % 2) % 3` after reducing the base, and `S % 2 = 1`. -/
theorem padicValNat_two_pow_sub_one_odd {S : ℕ} (hS : Odd S) :
    padicValNat 3 (2 ^ S - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  -- Goal: ¬ 3 ∣ (2 ^ S - 1).  Show (2 ^ S - 1) % 3 = 1.
  have hmod : 2 ^ S % 3 = 2 := by
    have hbase : (2 : ℕ) % 3 = 2 := by decide
    -- 2^S ≡ (-1)^S ≡ -1 ≡ 2 (mod 3) for odd S; compute via 2 = 3 - 1.
    obtain ⟨k, rfl⟩ := hS
    -- 2^(2k+1) % 3 = 2
    induction k with
    | zero => decide
    | succ k ih =>
        have hstep : 2 ^ (2 * (k + 1) + 1) = 2 ^ (2 * k + 1) * 4 := by ring
        rw [hstep, Nat.mul_mod, ih]
  have hpos : 1 ≤ 2 ^ S := Nat.one_le_two_pow
  have hsub : (2 ^ S - 1) % 3 = 1 := by omega
  intro hdvd
  rw [Nat.dvd_iff_mod_eq_zero] at hdvd
  omega

/-! ### Combined statement -/

/-- **`ν₃(2^S − 1)`, full form (uncapped).** For `S ≠ 0`,
`ν₃(2^S − 1) = if Even S then 1 + ν₃(S) else 0`.

Even case: write `S = 2t`, apply `padicValNat_two_pow_sub_one_even`, then use
`ν₃(2t) = ν₃(t)` (since `3` is coprime to `2`, via `padicValNat.div'`).
Odd case: `padicValNat_two_pow_sub_one_odd`. -/
theorem padicValNat_two_pow_sub_one (S : ℕ) (hS : S ≠ 0) :
    padicValNat 3 (2 ^ S - 1) = if Even S then 1 + padicValNat 3 S else 0 := by
  rcases Nat.even_or_odd S with hev | hodd
  · rw [if_pos hev]
    obtain ⟨t, rfl⟩ := hev
    have ht : t ≠ 0 := by rintro rfl; simp at hS
    -- 2 * t : rewrite `t + t` produced by `Even` as `2 * t`.
    have htt : t + t = 2 * t := by ring
    rw [htt]
    rw [padicValNat_two_pow_sub_one_even t ht]
    -- Now reduce ν₃(2 * t) = ν₃(t).
    have hcop : Nat.Coprime 3 2 := by decide
    have hdvd : (2 : ℕ) ∣ 2 * t := Dvd.intro t rfl
    have hdiv : padicValNat 3 (2 * t / 2) = padicValNat 3 (2 * t) :=
      padicValNat.div' (p := 3) (m := 2) hcop hdvd
    rw [Nat.mul_div_cancel_left t (by norm_num)] at hdiv
    rw [hdiv]
  · rw [if_neg (by simpa [Nat.not_even_iff_odd] using hodd)]
    exact padicValNat_two_pow_sub_one_odd hodd

/-! ### Bridge: capped `nu3` ↔ uncapped `padicValNat 3`

The project's `nu3 n c` is `padicValNat 3 n` capped at `c`. When the cap is not
binding (`padicValNat 3 n < c`), the two coincide. This is the transport lemma
that lets the LTE results above feed the existing `rhoPlus` / `deltaPlus`
framework. -/

/-- **Bridge lemma.** If `n ≠ 0` and the true 3-adic valuation is strictly
below the cap (`padicValNat 3 n < c`), then the project's capped `nu3 n c`
equals Mathlib's `padicValNat 3 n`.

Proof by induction on the cap `c`, mirroring the recursion of `nu3`. The
strict inequality `< c` is exactly what guarantees the cap never truncates:
at each `3 ∣ n` step it lets us peel one factor of 3 (decreasing both the value
by `1` via `padicValNat.div` and the cap by `1`), and at a `3 ∤ n` step both
sides are `0`. -/
theorem nu3_eq_padicValNat_of_lt (n c : ℕ) (hn : n ≠ 0)
    (hlt : padicValNat 3 n < c) : nu3 n c = padicValNat 3 n := by
  induction c generalizing n with
  | zero => exact absurd hlt (Nat.not_lt_zero _)
  | succ c ih =>
      unfold nu3
      rw [if_neg hn]
      by_cases h3 : n % 3 = 0
      · -- 3 ∣ n: peel a factor of 3.
        rw [if_pos h3]
        have hdvd : (3 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero h3
        have hq : n / 3 ≠ 0 := by
          intro hq0
          rw [Nat.div_eq_zero_iff] at hq0
          omega
        -- padicValNat 3 n = padicValNat 3 (n/3) + 1, and ≥ 1.
        have hval : padicValNat 3 (n / 3) = padicValNat 3 n - 1 :=
          padicValNat.div (p := 3) hdvd
        have hge1 : 1 ≤ padicValNat 3 n :=
          one_le_padicValNat_of_dvd hn hdvd
        have hlt' : padicValNat 3 (n / 3) < c := by
          rw [hval]; omega
        rw [ih (n / 3) hq hlt', hval]
        omega
      · -- 3 ∤ n: both sides 0.
        rw [if_neg h3]
        have hnd : ¬ (3 : ℕ) ∣ n := by
          rw [Nat.dvd_iff_mod_eq_zero]; exact h3
        rw [padicValNat.eq_zero_of_not_dvd hnd]

end CollatzLean4.Admissible
