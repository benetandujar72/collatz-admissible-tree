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

end CollatzLean4.Admissible
