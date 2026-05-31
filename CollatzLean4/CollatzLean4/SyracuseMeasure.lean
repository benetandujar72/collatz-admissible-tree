/-
Copyright (c) 2026 Benet Andújar Guardado.

S239 — PROJECT (c2): the measure-theoretic infrastructure for the Syracuse DISTRIBUTION
(the probabilistic / Tao-2019 side of the coupling). LONG horizon, built methodically.

WHY. `Coupling.lean` proved the EXACT (deterministic) Syracuse identity `2^{A_m}·Syr^m a₀ ≡ C_m
(mod 3^m)` — the m-th iterate's residue is determined by the 2-adic valuation sequence. Tao (2019)
studies the DISTRIBUTION of this residue when the valuations are replaced by i.i.d. Geometric(2)
random variables (`P(ν₂ = k) = 2^{-k}`), and proves the resulting law on `(ℤ/3^n)^×` has full
support / near-equidistribution (the strongest unconditional Collatz result). That distributional
layer needs infrastructure ABSENT from Mathlib; this module builds it from the ground up.

BLUEPRINT (dependency order; each is a milestone):
  1. [THIS FILE, first] `valPMF` : the Geometric(2) law of a single valuation, `P(k)=2^{-(k+1)}`
     (index k ↦ valuation k+1, since ν₂(3n+1) ≥ 1). — the atomic 2-adic object.
  2. The product law on valuation sequences `Fin m → ℕ` (`PMF.bind`/independence).
  3. `syracuseLaw m : PMF (ZMod (3^m))` — the pushforward of (2) under the offset map
     `(aᵢ) ↦ 2^{-A_m}·C_m` (= our deterministic `cycleC`, scaled). This is `Syrac(ℤ/3^m)`.
  4. The CHARACTERISTIC FUNCTION `Ê(ξ) = 𝔼 exp(-2πi ξ·Syrac/3^m)` via Mathlib `AddChar (ZMod 3^m)`
     (Mathlib HAS finite Fourier: AddChar, gaussSum, Pontryagin duality on finite abelian groups).
  5. Its Riesz-product factorization (independence ⟹ the char. fn is a product over coordinates).
  6. THE HARD CORE: the super-polynomial decay `|Ê(ξ)| ≪_A n^{-A}` for `3 ∤ ξ` (Tao's Prop 1.17;
     the renewal / large-deviation estimate). This is the genuine research mountain.
  7. Support / equidistribution corollaries.

HONEST SCOPE: milestones 1–5 are foundational and formalizable (this is real, careful work, not a
proof of Collatz). Milestone 6 is research-grade and where the difficulty concentrates; even Tao
obtains only "almost all". We start at 1 and build up, with calm.
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import CollatzLean4.CycleEquation

namespace CollatzLean4.Admissible

open scoped ENNReal

/-- **The valuation law (Geometric(2)).** `valPMF` is the probability mass function of a single
2-adic valuation `ν₂(3n+1)`: the value `k` (representing valuation `k+1`, since `ν₂ ≥ 1`) has mass
`2^{-(k+1)}`. Milestone 1 of the Syracuse-distribution blueprint — the atomic 2-adic object. -/
noncomputable def valPMF : PMF ℕ :=
  ⟨fun k => (2 : ℝ≥0∞)⁻¹ ^ (k + 1), by
    have hpow : ∀ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ k := by
      intro k; rw [pow_succ, mul_comm]
    have hsum : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = 1 := by
      simp_rw [hpow]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      have h12 : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
        rw [← ENNReal.inv_two_add_inv_two, ENNReal.add_sub_cancel_left (by simp)]
      rw [h12]
      exact ENNReal.mul_inv_cancel (by simp) (by simp)
    rw [← hsum]
    exact ENNReal.summable.hasSum⟩

/-- The valuation law assigns mass `0` to `k = 0` is FALSE here — index `k` encodes valuation `k+1`,
so `valPMF 0 = 2⁻¹` is the mass of valuation `1` (the most likely). Basic value lemma. -/
@[simp] theorem valPMF_apply (k : ℕ) : valPMF k = (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := rfl

/-- Every valuation has positive probability: `valPMF` has full support on `ℕ` (the 2-adic
valuation `ν₂(3n+1)` is unbounded). -/
theorem valPMF_pos (k : ℕ) : 0 < valPMF k := by
  rw [valPMF_apply, pos_iff_ne_zero]
  exact pow_ne_zero _ (by simp)

/-- **The valuation-sequence law (Milestone 2).** The joint law of `m` independent valuations,
`valSeqPMF m : PMF (Fin m → ℕ)`, each coordinate distributed as `valPMF`, built by appending one
fresh valuation at a time via `Fin.snoc`. This is the product law of `(a₀,…,a_{m-1})` underlying
Tao's Syracuse random variable; the next milestone pushes it forward under the offset map. -/
noncomputable def valSeqPMF : (m : ℕ) → PMF (Fin m → ℕ)
  | 0 => PMF.pure (Fin.elim0)
  | (m + 1) => (valSeqPMF m).bind fun a => valPMF.map (Fin.snoc a)

/-- The valuation tuple `a : Fin m → ℕ` extended to a sequence `ℕ → ℕ` (zero past `m`), so the
deterministic `partialA`/`cycleC` (defined on `ℕ → ℕ`) apply. Only indices `< m` are used. -/
def extendVal {m : ℕ} (a : Fin m → ℕ) : ℕ → ℕ :=
  fun i => if h : i < m then a ⟨i, h⟩ else 0

/-- **The Syracuse offset map (Milestone 3 core).** Given the valuation tuple `a : Fin m → ℕ`, the
residue `2^{-A_m}·C_m ∈ ZMod (3^m)` (with `A_m = Σ aᵢ = partialA`, `C_m = cycleC`) — exactly the
residue the EXACT identity `2^{A_m}·a_m ≡ C_m (mod 3^m)` solves for. Reuses the deterministic
`partialA`/`cycleC`, tying the distribution to the proven identity. -/
noncomputable def syracuseOffset {m : ℕ} (a : Fin m → ℕ) : ZMod (3 ^ m) :=
  Ring.inverse ((2 : ZMod (3 ^ m)) ^ (partialA (extendVal a) m))
    * ((cycleC (extendVal a) m : ℕ) : ZMod (3 ^ m))

/-- **The Syracuse law (Milestone 3) = Tao's Syracuse random variable `Syrac(ℤ/3^m)`.** The
pushforward of the valuation-sequence law under the offset map: the distribution of the residue of
an `m`-step Syracuse orbit mod `3^m` when the valuations are i.i.d. Geometric(2). -/
noncomputable def syracuseLaw (m : ℕ) : PMF (ZMod (3 ^ m)) :=
  (valSeqPMF m).map syracuseOffset

/-- **The offset is correct.** `2^{A_m}·syracuseOffset a = C_m` in `ZMod (3^m)` — the offset map
genuinely solves the exact Syracuse identity (so `syracuseLaw` is the law of the actual residue,
not a vacuous definition). From the unit-ness of `2^{A_m}` and `Ring.mul_inverse_cancel`. -/
theorem syracuseOffset_spec {m : ℕ} (a : Fin m → ℕ) :
    (2 : ZMod (3 ^ m)) ^ (partialA (extendVal a) m) * syracuseOffset a
      = ((cycleC (extendVal a) m : ℕ) : ZMod (3 ^ m)) := by
  have h2 : IsUnit (2 : ZMod (3 ^ m)) := by
    have hcast : ((2 : ℕ) : ZMod (3 ^ m)) = (2 : ZMod (3 ^ m)) := by push_cast; ring
    rw [← hcast, ZMod.isUnit_iff_coprime]
    exact (by decide : Nat.Coprime 2 3).pow_right m
  unfold syracuseOffset
  rw [← mul_assoc, Ring.mul_inverse_cancel _ (h2.pow _), one_mul]

/-! ### Support ⊆ units (the easy half of Tao's support, deterministic) -/

/-- The offset constant `cycleC k m` is coprime to 3 (for `m ≥ 1`): `cycleC k (m'+1) = 3·cycleC + 2^A`
is `≡ 2^A ≢ 0 (mod 3)`. -/
theorem cycleC_coprime_three (k : ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m) : Nat.Coprime (cycleC k m) 3 := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hrec : cycleC k (m' + 1) = 3 * cycleC k m' + 2 ^ (partialA k m') := rfl
  have h3 : ¬ (3 : ℕ) ∣ cycleC k (m' + 1) := by
    rw [hrec]
    have hnd : ¬ (3 : ℕ) ∣ 2 ^ (partialA k m') := by
      intro hd; have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd; omega
    omega
  exact ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm

/-- **The Syracuse offset is always a unit** (`m ≥ 1`): `2^{-A_m}·C_m` is a product of two units
(`2^{A_m}` and `C_m`, both coprime to 3). So the Syracuse residue avoids the multiples of 3. -/
theorem syracuseOffset_isUnit {m : ℕ} (hm : 1 ≤ m) (a : Fin m → ℕ) :
    IsUnit (syracuseOffset a) := by
  have h2 : IsUnit (2 : ZMod (3 ^ m)) := by
    have hcast : ((2 : ℕ) : ZMod (3 ^ m)) = (2 : ZMod (3 ^ m)) := by push_cast; ring
    rw [← hcast, ZMod.isUnit_iff_coprime]
    exact (by decide : Nat.Coprime 2 3).pow_right m
  unfold syracuseOffset
  refine IsUnit.mul ?_ ?_
  · apply IsUnit.of_mul_eq_one
    exact Ring.inverse_mul_cancel _ (h2.pow _)
  · exact (ZMod.isUnit_iff_coprime _ _).mpr ((cycleC_coprime_three (extendVal a) m hm).pow_right m)

/-- **Support ⊆ units (Tao's support, easy half).** Every residue in the support of `syracuseLaw m`
(`m ≥ 1`) is a unit mod `3^m` — the Syracuse random variable "always avoids multiples of 3", as an
exact deterministic fact via `PMF.mem_support_map_iff`. The HARD half (every unit IS attained = the
offset map is surjective onto units) is the remaining reachability frontier. -/
theorem syracuseLaw_support_isUnit {m : ℕ} (hm : 1 ≤ m) {b : ZMod (3 ^ m)}
    (hb : b ∈ (syracuseLaw m).support) : IsUnit b := by
  rw [syracuseLaw, PMF.mem_support_map_iff] at hb
  obtain ⟨a, _, rfl⟩ := hb
  exact syracuseOffset_isUnit hm a

end CollatzLean4.Admissible
