/-
Copyright (c) 2026 Benet Andújar Guardado.

S239 — PROJECT (c): attacking the 2-adic ⊗ 3-adic coupling (long horizon).

The genuine open core of Wall B is the COUPLING: how the 2-adic valuations `ν₂(3n+1)` (which
choose the inverse-Collatz branch) interact with the 3-adic discrete-log structure. The right
conceptual framework (converged from the cross-disciplinary survey):

  * The inverse-Collatz dynamics on `(ℤ/3^k)^×` is a SKEW PRODUCT — a 3-adic discrete-log cocycle
    over the 2-adic ν₂ choices — equivalently an ITERATED FUNCTION SYSTEM on dlog coordinates,
    whose branches are indexed by `ν₂` (one-edges translate dlog by `τ`; zero-edges apply the
    analytic `log₃` jump and lift the level).
  * At ONE step, the valid 2-adic exponents `a` (those with `2^a c ≡ 1 mod 3`) have FIXED PARITY,
    so `2^a` ranges over a coset of `⟨4⟩ = ⟨2²⟩` — the squares / even-dlog subgroup. Thus the
    per-step "2-adic choice" is a coset of the quadratic-residue subgroup.
  * Reachability of trap residues = the IFS orbit / support. (Tao: full support on the units
    UNCONDITIONALLY; the open part is the admissible-cylinder constraint.)

This module is the first front of that attack. First brick: identify the per-step coset structure
by characterizing the quadratic-residue subgroup via the (proven) discrete log.
0 sorry / 0 ad-hoc axiom.
-/

import CollatzLean4.DlogReachable
import CollatzLean4.CycleEquation

namespace CollatzLean4.Admissible

/-- A unit of `ZMod (3^k)` is a SQUARE iff its discrete log is even. (`2^d = (2^{d/2})²` iff d
even; conversely `dlog(a²) ≡ 2·dlog a` is even, and the order `2·3^{k-1}` is even, so it stays
even.) The squares are exactly the even-dlog subgroup `⟨4⟩ = ⟨2²⟩`. -/
theorem isSquare_iff_dlog_even (k : ℕ) (hk : 1 ≤ k) {c : ZMod (3 ^ k)} (hc : IsUnit c) :
    IsSquare c ↔ dlog k c % 2 = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    have ha : IsUnit a := (IsUnit.mul_iff.mp hc).1
    have hmod2 : dlog k (a * a) % 2 = (dlog k a + dlog k a) % 2 :=
      Nat.ModEq.of_dvd ⟨3 ^ (k - 1), rfl⟩ (dlog_mul k hk ha ha)
    omega
  · intro he
    obtain ⟨e, he'⟩ : ∃ e, dlog k c = 2 * e := ⟨dlog k c / 2, by omega⟩
    exact ⟨(2 : ZMod (3 ^ k)) ^ e, by rw [← two_pow_dlog k hk hc, he', two_mul, pow_add]⟩

/-- **Squares mod 3^k = units ≡ 1 (mod 3).** The quadratic-residue subgroup `⟨4⟩ = ⟨2²⟩` (the
even-dlog units) is exactly `{c ≡ 1 mod 3}` — the quadratic character IS the mod-3 sign. This is
the per-step "2-adic choice" coset of the inverse-Collatz dynamics, tied here to the 3-adic sign:
the first verified structural brick connecting the 2-adic branch structure to the 3-adic
discrete log. -/
theorem isSquare_iff_mod_three (k : ℕ) (hk : 1 ≤ k) {c : ℕ} (hco : Nat.Coprime c 3) :
    IsSquare ((c : ZMod (3 ^ k))) ↔ c % 3 = 1 := by
  have hunit : IsUnit ((c : ZMod (3 ^ k))) :=
    (ZMod.isUnit_iff_coprime c (3 ^ k)).mpr (hco.pow_right k)
  have hc3 : c % 3 ≠ 0 := by
    have := (Nat.prime_three.coprime_iff_not_dvd).mp hco.symm; omega
  rw [isSquare_iff_dlog_even k hk hunit, dlog_mod_two k c hk hco]
  by_cases h : c % 3 = 2
  · rw [if_pos h]
    exact ⟨fun h1 => absurd h1 (by decide), fun h1 => by omega⟩
  · rw [if_neg h]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- **THE FIRST 2↔3 COUPLING LINK (verified).** The 3-adic SIGN of the Syracuse successor equals
the parity of the 2-adic VALUATION: `Syr n ≡ 1 mod 3` if `ν₂(3n+1)` is even, `≡ 2 mod 3` if odd.
A 2-adic quantity (`ν₂`) is thereby locked to a 3-adic quantity (the sign `[Syr n ≡ 2 mod 3]`) —
the project's first direct bridge between the two filtrations. (Proof: `2^{ν₂}·Syr n = 3n+1 ≡ 1
mod 3` and `2^{ν₂} ≡ (−1)^{ν₂} mod 3`.) -/
theorem syr_succ_mod_three (n : ℕ) :
    (Syr n) % 3 = if (padicValNat 2 (3 * n + 1)) % 2 = 0 then 1 else 2 := by
  have hstep := Syr_step n
  have h1 : (2 ^ (padicValNat 2 (3 * n + 1)) * Syr n) % 3 = 1 := by rw [hstep]; omega
  rw [Nat.mul_mod, two_pow_mod_three] at h1
  by_cases hν : (padicValNat 2 (3 * n + 1)) % 2 = 0
  · rw [if_pos hν] at h1 ⊢; omega
  · rw [if_neg hν] at h1 ⊢; omega

/-- The same coupling, as the parity identity `[Syr n ≡ 2 mod 3] = ν₂(3n+1) mod 2`. -/
theorem syr_succ_sign_eq_nu2_parity (n : ℕ) :
    (if (Syr n) % 3 = 2 then 1 else 0) = (padicValNat 2 (3 * n + 1)) % 2 := by
  rw [syr_succ_mod_three]
  by_cases hν : (padicValNat 2 (3 * n + 1)) % 2 = 0
  · simp [hν]
  · have h1 : (padicValNat 2 (3 * n + 1)) % 2 = 1 := by omega
    simp [h1]

end CollatzLean4.Admissible
