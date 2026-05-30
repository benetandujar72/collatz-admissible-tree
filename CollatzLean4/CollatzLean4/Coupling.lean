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

end CollatzLean4.Admissible
