/-
Copyright (c) 2026 Benet Andújar Guardado.

S239 — Discrete-log foundation mod 3^k: the order of 2 (Wall-B scaffolding).

Both Collatz walls reduce to the discrete logarithm base 2 mod 3^k:
  * Wall A (cycles) needs |2^A − 3^m| effective lower bounds (archimedean side);
  * Wall B (slope barrier) needs the 3-adic distribution of `ν₃(c − 2^τ)`, i.e.
    `c ≡ 2^τ (mod 3^j)` — a discrete-log condition (3-adic side).
The bridge is the multiplicative order of 2 mod 3^k. Since 2 is a primitive root
mod 3^k, that order is `φ(3^k) = 2·3^{k-1}`.

This module proves the order law DIRECTLY from the project's lifting-the-exponent
law `padicValNat_two_pow_sub_one` (a real reuse), upgrades the closed-walk weight
bound from `≥` to EXACT divisibility by the order, and computes
`orderOf (2 : ZMod (3^k))`. Reusable, Mathlib-quality discrete-log infrastructure.
0 sorry / 0 ad-hoc axiom.
-/

import CollatzLean4.ClosedWalk
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.QuotientGroup

namespace CollatzLean4.Admissible

/-- `3^k ∣ n ↔ k ≤ ν₃(n)` (for `n ≠ 0`). -/
theorem three_pow_dvd_iff_le (n k : ℕ) (hn : n ≠ 0) :
    3 ^ k ∣ n ↔ k ≤ padicValNat 3 n := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp3 hn, Nat.factorization_def n hp3]

/-- **Order of 2 mod 3^k, divisibility form.** For `k, d ≥ 1`,
`3^k ∣ 2^d − 1 ⟺ 2·3^{k-1} ∣ d`. Proven directly from the LTE law
`ν₃(2^d − 1) = (Even d ? 1 + ν₃(d) : 0)`. Hence `2·3^{k-1}` is exactly the
multiplicative order of 2 mod 3^k — i.e. 2 is a primitive root. -/
theorem two_pow_three_pow_dvd_iff (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    3 ^ k ∣ (2 ^ d - 1) ↔ 2 * 3 ^ (k - 1) ∣ d := by
  have hd0 : d ≠ 0 := by omega
  have h2d0 : 2 ^ d - 1 ≠ 0 := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    simp only [pow_one] at h2; omega
  rw [three_pow_dvd_iff_le _ _ h2d0, padicValNat_two_pow_sub_one d hd0]
  constructor
  · intro hle
    by_cases hev : Even d
    · rw [if_pos hev] at hle
      have hh2 : 2 ∣ d := hev.two_dvd
      have hh3 : 3 ^ (k - 1) ∣ d := (three_pow_dvd_iff_le d (k - 1) hd0).mpr (by omega)
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        ((by decide : Nat.Coprime 2 3).pow_right _) hh2 hh3
    · rw [if_neg hev] at hle; omega
  · intro hdvd
    have hh2 : 2 ∣ d := dvd_trans ⟨3 ^ (k - 1), by ring⟩ hdvd
    have hh3 : 3 ^ (k - 1) ∣ d := dvd_trans ⟨2, by ring⟩ hdvd
    have hev : Even d := by obtain ⟨c, hc⟩ := hh2; exact ⟨c, by omega⟩
    rw [if_pos hev]
    have hle3 : k - 1 ≤ padicValNat 3 d := (three_pow_dvd_iff_le d (k - 1) hd0).mp hh3
    omega

/-- **Closed-walk weight is an EXACT multiple of the order of 2.** Upgrades
`closed_oneWalk_weight_ge_order` (a `≥` bound) to divisibility: a nontrivial closed
one-edge walk has weight `W` divisible by `2·3^{R+j-1} = ord(2 mod 3^{R+j})`. -/
theorem closed_oneWalk_order_dvd {R : ℕ} {v₀ : InvVertex} {w : ℤ}
    {vs : List InvVertex} (hX : InX v₀.c) (hk : 1 ≤ R + v₀.j) (hpos : 0 < w)
    (h : WPath (InvEdgeOne R) v₀ v₀ w vs) :
    ∃ E : ℕ, (E : ℤ) = w ∧ 2 * 3 ^ (R + v₀.j - 1) ∣ E := by
  obtain ⟨E, hE, hmod⟩ := closed_oneWalk_two_pow_mod hX h
  refine ⟨E, hE, ?_⟩
  have hE1 : 1 ≤ E := by
    rcases Nat.eq_zero_or_pos E with h0 | h0
    · exfalso; rw [h0] at hE; simp only [Nat.cast_zero] at hE; omega
    · exact h0
  have h1le : (1 : ℕ) ≤ 2 ^ E := Nat.one_le_two_pow
  have hdvd : 3 ^ (R + v₀.j) ∣ (2 ^ E - 1) := (Nat.modEq_iff_dvd' h1le).mp hmod.symm
  exact (two_pow_three_pow_dvd_iff (R + v₀.j) E hk hE1).mp hdvd

/-- **Order of 2 in `ZMod (3^k)`.** `orderOf (2 : ZMod (3^k)) = 2·3^{k-1}` for
`k ≥ 1` — i.e. **2 is a primitive root mod 3^k**, generating the full unit group of
order `φ(3^k) = 2·3^{k-1}`. Derived from the divisibility law above. This is the
clean Mathlib-facing statement of the discrete-log backbone. -/
theorem orderOf_two_zmod_three_pow (k : ℕ) (hk : 1 ≤ k) :
    orderOf (2 : ZMod (3 ^ k)) = 2 * 3 ^ (k - 1) := by
  have key : ∀ d, 1 ≤ d →
      ((2 : ZMod (3 ^ k)) ^ d = 1 ↔ 2 * 3 ^ (k - 1) ∣ d) := by
    intro d hd
    have hle : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
    have e2 : (2 : ZMod (3 ^ k)) ^ d = ((2 ^ d : ℕ) : ZMod (3 ^ k)) := by push_cast; ring
    have e1 : (1 : ZMod (3 ^ k)) = ((1 : ℕ) : ZMod (3 ^ k)) := by push_cast; ring
    rw [e2, e1, ZMod.natCast_eq_natCast_iff, ← two_pow_three_pow_dvd_iff k d hk hd]
    exact ⟨fun hh => (Nat.modEq_iff_dvd' hle).mp hh.symm,
           fun hh => ((Nat.modEq_iff_dvd' hle).mpr hh).symm⟩
  have hN1 : 0 < 2 * 3 ^ (k - 1) := by positivity
  have hdvd_ord : orderOf (2 : ZMod (3 ^ k)) ∣ 2 * 3 ^ (k - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact (key _ hN1).mpr (dvd_refl _)
  refine Nat.dvd_antisymm hdvd_ord ?_
  have hpos : 0 < orderOf (2 : ZMod (3 ^ k)) :=
    Nat.pos_of_dvd_of_pos hdvd_ord hN1
  exact (key _ hpos).mp (pow_orderOf_eq_one _)

/-! ### Discrete log exists: every unit mod 3^k is a power of 2 -/

/-- **Discrete log exists mod 3^k.** Since 2 is a primitive root
(`orderOf_two_zmod_three_pow`), it generates the unit group, so every unit `c` of
`ZMod (3^k)` is a natural power `2^t` — its discrete logarithm `t = dlog(c)`.

This is the **Wall-B reformulation primitive**. Combined with the divisibility law, the
one-edge ρ₊-lift satisfies `ν₃(c − 2^τ) ≥ j ⟺ c ≡ 2^τ (mod 3^j) ⟺ dlog(c) ≡ τ (mod 2·3^{j-1})`,
recasting the slope-barrier residual as a REACHABILITY question on discrete-log
residues along κ-paths — NOT an equidistribution/discrepancy question (which would be
Tier-3 / open). -/
theorem exists_two_pow_eq_of_isUnit (k : ℕ) (hk : 1 ≤ k)
    {c : ZMod (3 ^ k)} (hc : IsUnit c) :
    ∃ t : ℕ, (2 : ZMod (3 ^ k)) ^ t = c := by
  haveI : NeZero (3 ^ k) := ⟨by positivity⟩
  have h2unit : IsUnit (2 : ZMod (3 ^ k)) := by
    have hcast : ((2 : ℕ) : ZMod (3 ^ k)) = (2 : ZMod (3 ^ k)) := by push_cast; ring
    rw [← hcast, ZMod.isUnit_iff_coprime]
    exact (by decide : Nat.Coprime 2 3).pow_right k
  obtain ⟨u, hu⟩ := h2unit
  obtain ⟨v, hv⟩ := hc
  have hou : orderOf u = 2 * 3 ^ (k - 1) := by
    rw [← orderOf_units, hu, orderOf_two_zmod_three_pow k hk]
  have hcard : Nat.card (ZMod (3 ^ k))ˣ = 3 ^ (k - 1) * 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_three (by omega)]
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hou, hcard]; ring
  have hmem : v ∈ Subgroup.zpowers u := by rw [htop]; exact Subgroup.mem_top v
  have hv_pow : ∃ t : ℕ, u ^ t = v := by
    rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨t, ht⟩ := hv_pow
  refine ⟨t, ?_⟩
  have e : (2 : ZMod (3 ^ k)) ^ t = ((u ^ t : (ZMod (3 ^ k))ˣ) : ZMod (3 ^ k)) := by
    rw [← hu]; push_cast; ring
  rw [e, ht]; exact hv

/-- **The ρ₊-lift is a congruence (Wall-B reformulation, congruence form).**
`3^j ∣ (c − 2^t) ⟺ 2^t ≡ c (mod 3^j)` — the one-edge jump depth `ν₃(c − 2^t)` is
exactly how deep `c` agrees with `2^t`. With `exists_two_pow_eq_of_isUnit` this is the
discrete-log congruence `dlog(c) ≡ t (mod 2·3^{j-1})`. -/
theorem three_pow_dvd_sub_iff_modEq (c t j : ℕ) (h : 2 ^ t ≤ c) :
    3 ^ j ∣ (c - 2 ^ t) ↔ 2 ^ t ≡ c [MOD 3 ^ j] :=
  (Nat.modEq_iff_dvd' h).symm

end CollatzLean4.Admissible
