/-
S240 — The full-Collatz ↔ Syracuse bridge: instantiating `SyrVerifiedUpTo` from the
literature's verification statement.

The cycle-reduction pipeline (CycleReduction.lean) consumes `SyrVerifiedUpTo X₀` — a
statement about the ACCELERATED Syracuse map `Syr n = (3n+1)/2^{ν₂(3n+1)}`.  The
literature's computational verification (Barina, *J. Supercomputing* 2020: every
`n ≤ 704·2⁶⁰` converges) is about the FULL Collatz map `n ↦ n/2 | 3n+1`.  This module
proves the bridge:

  `CollatzVerifiedUpTo (3X+1)  →  SyrVerifiedUpTo X`

The core is `syrReaches1_of_collatzReaches1`: for ODD `n`, the Syracuse orbit is the odd
subsequence of the Collatz orbit — one Syracuse step `n ↦ Syr n` is exactly `1 + ν₂(3n+1)`
Collatz steps (`collatz_iterate_to_syr`), so the Collatz hitting time of `1` strictly
decreases along Syracuse steps (strong induction).  Even `n` enter odd-land in one
Syracuse step (`Syr n = 3n+1 ≤ 3X+1`), whence the `3X+1` slack.

With this, the headline instances become conditional on the LITERATURE's hypothesis
shape: `collatz_no_cycle_below_359` (needs verification ≤ 3·2²⁰+1 ≈ 3.1·10⁶) and
`collatz_no_cycle_below_16266` (needs ≤ 3·2²⁹+1 ≈ 1.6·10⁹) — both far below `704·2⁶⁰`.
The hypothesis remains explicit throughout: stated, never asserted.

No native_decide; axioms {propext, Classical.choice, Quot.sound}.  Builds narrow.
-/

import CollatzLean4.CycleReduction

namespace CollatzLean4.Admissible

/-- The full Collatz map: `n/2` for even `n`, `3n+1` for odd `n`. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` reaches `1` under the full Collatz iteration. -/
def CollatzReaches1 (n : ℕ) : Prop := ∃ k, (collatz^[k]) n = 1

/-- The literature's verification statement (true for `X = 704·2⁶⁰` per Barina 2020) —
an EXPLICIT hypothesis here, never asserted. -/
def CollatzVerifiedUpTo (X : ℕ) : Prop := ∀ n, 0 < n → n ≤ X → CollatzReaches1 n

/-! ### The halving prefix -/

/-- The first `i ≤ v` Collatz steps from `2^v · q` are halvings. -/
theorem collatz_iterate_halving_le (q : ℕ) :
    ∀ i v, i ≤ v → (collatz^[i]) (2 ^ v * q) = 2 ^ (v - i) * q := by
  intro i
  induction i with
  | zero => intro v _; simp
  | succ i ih =>
      intro v hiv
      have hv : 1 ≤ v := by omega
      rw [Function.iterate_succ_apply]
      have he2 : (2 : ℕ) ^ v = 2 * 2 ^ (v - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hx : collatz (2 ^ v * q) = 2 ^ (v - 1) * q := by
        unfold collatz
        have heven : (2 ^ v * q) % 2 = 0 := by
          have hd : (2 : ℕ) ∣ 2 ^ v * q :=
            Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) q
          omega
        rw [if_pos heven]
        have ha : 2 ^ v * q = 2 * (2 ^ (v - 1) * q) := by rw [he2]; ring
        rw [ha]
        omega
      rw [hx, ih (v - 1) (by omega)]
      congr 2
      omega

/-- One Syracuse step on an odd `n` is exactly `ν₂(3n+1) + 1` Collatz steps. -/
theorem collatz_iterate_to_syr (n : ℕ) (hodd : n % 2 = 1) :
    (collatz^[padicValNat 2 (3 * n + 1) + 1]) n = Syr n := by
  rw [Function.iterate_succ_apply]
  have h1 : collatz n = 3 * n + 1 := by
    unfold collatz
    rw [if_neg (by omega)]
  rw [h1]
  have hstep := Syr_step n
  have hpos : 0 < Syr n := Syr_pos n
  calc (collatz^[padicValNat 2 (3 * n + 1)]) (3 * n + 1)
      = (collatz^[padicValNat 2 (3 * n + 1)])
          (2 ^ padicValNat 2 (3 * n + 1) * Syr n) := by rw [hstep]
    _ = 2 ^ (padicValNat 2 (3 * n + 1) - padicValNat 2 (3 * n + 1)) * Syr n :=
        collatz_iterate_halving_le (Syr n) _ _ (le_refl _)
    _ = Syr n := by rw [Nat.sub_self, pow_zero, one_mul]

/-! ### The bridge for odd numbers (strong induction on the Collatz hitting time) -/

/-- **If the Collatz orbit of an odd `n` reaches `1`, so does its Syracuse orbit.**
The Syracuse successor sits on the Collatz orbit at time `ν₂(3n+1) + 1 ≥ 2`, so its
Collatz hitting time is strictly smaller; strong induction. -/
theorem syrReaches1_of_collatzReaches1 :
    ∀ j n, n % 2 = 1 → (collatz^[j]) n = 1 → SyrReaches1 n := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro n hodd hj
    by_cases h1 : n = 1
    · exact ⟨0, by rw [h1]; rfl⟩
    · have hodd' : ¬ 2 ∣ n := by omega
      have hν1 : 1 ≤ padicValNat 2 (3 * n + 1) := one_le_val_three_mul_add_one hodd'
      have hstep := Syr_step n
      have hspos : 0 < Syr n := Syr_pos n
      have hsodd : Syr n % 2 = 1 := by
        have := Syr_not_two_dvd n
        omega
      have hj0 : j ≠ 0 := by
        intro h0
        rw [h0] at hj
        exact h1 hj
      -- the hitting time exceeds the halving prefix
      have hjge : padicValNat 2 (3 * n + 1) + 1 ≤ j := by
        by_contra hlt
        push_neg at hlt
        have hj1 : (collatz^[j]) n = (collatz^[j - 1]) (3 * n + 1) := by
          have hsplit : j = (j - 1) + 1 := by omega
          conv_lhs => rw [hsplit]
          rw [Function.iterate_succ_apply]
          have hc : collatz n = 3 * n + 1 := by
            unfold collatz
            rw [if_neg (by omega)]
          rw [hc]
        have hhalf : (collatz^[j - 1]) (3 * n + 1)
            = 2 ^ (padicValNat 2 (3 * n + 1) - (j - 1)) * Syr n := by
          calc (collatz^[j - 1]) (3 * n + 1)
              = (collatz^[j - 1]) (2 ^ padicValNat 2 (3 * n + 1) * Syr n) := by
                rw [hstep]
            _ = 2 ^ (padicValNat 2 (3 * n + 1) - (j - 1)) * Syr n :=
                collatz_iterate_halving_le (Syr n) _ _ (by omega)
        rw [hj1, hhalf] at hj
        have hd : (2 : ℕ) ∣ 2 ^ (padicValNat 2 (3 * n + 1) - (j - 1)) * Syr n :=
          Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
        omega
      -- the Syracuse successor's strictly smaller hitting time
      have hs : (collatz^[j - (padicValNat 2 (3 * n + 1) + 1)]) (Syr n) = 1 := by
        have hsplit : j = (j - (padicValNat 2 (3 * n + 1) + 1))
            + (padicValNat 2 (3 * n + 1) + 1) := by omega
        rw [hsplit, Function.iterate_add_apply, collatz_iterate_to_syr n hodd] at hj
        exact hj
      obtain ⟨k, hk⟩ := ih (j - (padicValNat 2 (3 * n + 1) + 1)) (by omega)
        (Syr n) hsodd hs
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-! ### The bridge -/

/-- **The bridge.**  Full-Collatz verification up to `3X+1` instantiates the Syracuse
verification hypothesis up to `X`: odd `n` directly; even `n` via its first Syracuse step
`Syr n = 3n+1 ≤ 3X+1` (odd). -/
theorem syrVerified_of_collatzVerified {X : ℕ} (hver : CollatzVerifiedUpTo (3 * X + 1)) :
    SyrVerifiedUpTo X := by
  intro n hn hX
  by_cases hodd : n % 2 = 1
  · obtain ⟨j, hj⟩ := hver n hn (by omega)
    exact syrReaches1_of_collatzReaches1 j n hodd hj
  · -- even n: Syr n = 3n+1 (odd), within the 3X+1 range
    have hSn : Syr n = 3 * n + 1 := by
      unfold Syr
      have hval : padicValNat 2 (3 * n + 1) = 0 := by
        rw [padicValNat.eq_zero_iff]
        right; right
        omega
      rw [hval, pow_zero, Nat.div_one]
    have h3odd : (3 * n + 1) % 2 = 1 := by omega
    obtain ⟨j, hj⟩ := hver (3 * n + 1) (by omega) (by omega)
    obtain ⟨k, hk⟩ := syrReaches1_of_collatzReaches1 j (3 * n + 1) h3odd hj
    exact ⟨k + 1, by rw [Function.iterate_succ_apply, hSn]; exact hk⟩

/-! ### The headline instances, with the literature's hypothesis shape -/

/-- Conditional on full-Collatz verification up to `3·2²⁰+1 ≈ 3.1·10⁶` (the literature
has `704·2⁶⁰ ≈ 8.1·10²⁰`): no nontrivial Syracuse cycle of period below `359`. -/
theorem collatz_no_cycle_below_359 (hver : CollatzVerifiedUpTo (3 * 2 ^ 20 + 1)) :
    NoSyrCycleBelowPeriod 359 :=
  syr_no_cycle_below_359 (syrVerified_of_collatzVerified hver)

/-- Conditional on full-Collatz verification up to `3·2²⁹+1 ≈ 1.6·10⁹` (the literature
has `704·2⁶⁰ ≈ 8.1·10²⁰`): no nontrivial Syracuse cycle of period below `16266`. -/
theorem collatz_no_cycle_below_16266 (hver : CollatzVerifiedUpTo (3 * 2 ^ 29 + 1)) :
    NoSyrCycleBelowPeriod 16266 :=
  syr_no_cycle_below_16266 (syrVerified_of_collatzVerified hver)

end CollatzLean4.Admissible
