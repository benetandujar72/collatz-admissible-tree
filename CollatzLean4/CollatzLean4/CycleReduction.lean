/-
S240 — Cycle reduction (the elementary foundation of the Hercher-style finite cycle bound).

Per the S240 Rhin–Viola scoping verdict: the Collatz cycle half is genuinely OPEN; the transcendence
route does NOT close it; the world-record FINITE bounds (no nontrivial Syracuse cycle of period below
~10^19, Hercher 2022) come from the CYCLE EQUATION + the computational verification frontier + a
continued-fraction ratchet — NOT from transcendence. This file builds the ELEMENTARY, unconditional
foundation of that route (step 1 of the recommended program), on top of `CycleEquation.lean`.

THE GAP `g := 2^{A_m} − 3^m`.  Step 1 = the subtractive cycle equation `g · a₀ = C_m`: the gap times
the cycle element equals the cycle constant.  With the corridor (`g ≥ 1`) and `a₀ ∣ C_m`, this is the
clean algebraic handle on which the verification-frontier coupling (step 2) and the continued-fraction
interval (step 3) will sit.  An ABSTRACT effective-linear-form socket (`EffectiveLinearForm`) is named
for any future Baker input — STATED, never assumed.

Pure ℕ algebra; 0 sorry, Baker-free, no native_decide, no aS202 anchors.
-/

import CollatzLean4.CycleEquation

namespace CollatzLean4.Admissible

/-! ### The cycle data of a Syracuse orbit (clean abbreviations) -/

/-- The 2-adic valuation sequence `k_i = ν₂(3·Syr^[i]a₀ + 1)` of a Syracuse orbit. -/
def cycleK (a0 : ℕ) : ℕ → ℕ := fun i => padicValNat 2 (3 * (Syr^[i]) a0 + 1)

/-- The cycle exponent `A_m = k₀ + ⋯ + k_{m-1}`. -/
def cycleA (a0 m : ℕ) : ℕ := partialA (cycleK a0) m

/-- The cycle constant `C_m = Σ_{i<m} 3^{m-1-i} 2^{A_i}`. -/
def cycleCm (a0 m : ℕ) : ℕ := cycleC (cycleK a0) m

/-- The cycle equation in cycle-data form: `2^{A_m}·a₀ = 3^m·a₀ + C_m`. -/
theorem syr_cycle_equation' (a0 m : ℕ) (h : (Syr^[m]) a0 = a0) :
    2 ^ cycleA a0 m * a0 = 3 ^ m * a0 + cycleCm a0 m :=
  syr_cycle_equation a0 m h

/-- The strict corridor in cycle-data form: `3^m < 2^{A_m}`. -/
theorem syr_cycle_corridor' (a0 m : ℕ) (hm : 0 < m) (h : (Syr^[m]) a0 = a0) :
    3 ^ m < 2 ^ cycleA a0 m :=
  syr_cycle_corridor a0 m hm h

/-! ### Step 1 — the subtractive cycle equation (the gap identity) -/

/-- **The subtractive cycle equation.**  A periodic point of `Syr` satisfies
`(2^{A_m} − 3^m) · a₀ = C_m`: the gap `g = 2^{A_m} − 3^m` times the cycle element equals the cycle
constant.  Pure ℕ algebra from the additive cycle equation. -/
theorem syr_cycle_gap_eq (a0 m : ℕ) (h : (Syr^[m]) a0 = a0) :
    (2 ^ cycleA a0 m - 3 ^ m) * a0 = cycleCm a0 m := by
  have heq := syr_cycle_equation' a0 m h
  rw [Nat.sub_mul]
  omega

/-- The gap is strictly positive for a genuine cycle (`m ≥ 1`): `0 < 2^{A_m} − 3^m`. -/
theorem syr_cycle_gap_pos (a0 m : ℕ) (hm : 0 < m) (h : (Syr^[m]) a0 = a0) :
    0 < 2 ^ cycleA a0 m - 3 ^ m := by
  have := syr_cycle_corridor' a0 m hm h
  omega

/-- The cycle element divides the cycle constant: `a₀ ∣ C_m` (with quotient the gap). -/
theorem syr_cycle_a0_dvd (a0 m : ℕ) (h : (Syr^[m]) a0 = a0) :
    a0 ∣ cycleCm a0 m :=
  ⟨2 ^ cycleA a0 m - 3 ^ m, by rw [← syr_cycle_gap_eq a0 m h]; ring⟩

/-- **The gap is bounded by `C_m / a₀`.**  For a positive cycle element, the gap satisfies
`(2^{A_m} − 3^m) · a₀ = C_m`, hence `2^{A_m} − 3^m ≤ C_m` (and `= C_m / a₀`).  This is the upper
bound on the gap that the verification-frontier coupling will sharpen: a LARGE minimum element `a₀`
forces a SMALL gap, i.e. `A_m / m` very close to `log₂3`. -/
theorem syr_cycle_gap_le (a0 m : ℕ) (ha0 : 0 < a0) (h : (Syr^[m]) a0 = a0) :
    2 ^ cycleA a0 m - 3 ^ m ≤ cycleCm a0 m := by
  have hg := syr_cycle_gap_eq a0 m h
  calc 2 ^ cycleA a0 m - 3 ^ m
      ≤ (2 ^ cycleA a0 m - 3 ^ m) * a0 := Nat.le_mul_of_pos_right _ ha0
    _ = cycleCm a0 m := hg

/-! ### The abstract effective-linear-form socket (for any future Baker input) -/

/-- **Abstract effective linear-form-in-logs hypothesis.**  `EffectiveLinearForm Φ` says the gap
`|2^A − 3^m|` is bounded below by an explicit `Φ A m` for all `A, m ≥ 1` (the archimedean input a
Baker/Matveev or Rhin–Viola theorem would supply).  This is the clean SOCKET into which any future
effective transcendence bound plugs.  It is NOT proven here and NOT assumed — it is the named
hypothesis under which the continued-fraction/verification argument would close periods beyond the
finite range.  (Per scoping: no such uniform effective theorem currently exists; the cycle half is
open.) -/
def EffectiveLinearForm (Φ : ℕ → ℕ → ℕ) : Prop :=
  ∀ A m : ℕ, 1 ≤ m → 3 ^ m < 2 ^ A → Φ A m ≤ 2 ^ A - 3 ^ m

end CollatzLean4.Admissible
