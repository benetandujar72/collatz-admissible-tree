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

/-! ### Step 1b — the upper corridor `A_m ≤ 2m` (the size branch, uniform in `m`)

S240, fruit of the unit-distance methodology review ("generalize the best known
construction"): multiplying the `m` step identities of a cycle gives the MULTIPLICATIVE
cycle equation `2^{A_m} · Π_{i<m} aᵢ = Π_{i<m} (3aᵢ + 1)`.  Since `3a + 1 ≤ 4a` for
`a ≥ 1` — strictly for `a ≥ 2` — every positive cycle has `2^{A_m} ≤ 4^m`, i.e.
`A_m ≤ 2m`, and every NONTRIVIAL cycle has `A_m < 2m`.  Combined with the strict lower
corridor `3^m < 2^{A_m}` this traps the exponent of a nontrivial cycle in the window
`m·log₂3 < A_m < 2m`, collapsing the "size branch" of the per-`m` finite analyses (the
`A ≥ 6` case of `m = 3`, the `A ≥ 8` case of `m = 4`) into ONE uniform theorem: the
residual per-`m` content is exactly the window `⌈m·log₂3⌉ ≤ A_m ≤ 2m − 1` that the
continued-fraction step of the Hercher-style reduction handles. -/

/-- House-style recursive product of the first `m` values of a sequence
(mirroring `partialA`/`cycleC`). -/
def seqProd (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | (m + 1) => seqProd a m * a m

theorem seqProd_pos (a : ℕ → ℕ) :
    ∀ m, (∀ i, i < m → 0 < a i) → 0 < seqProd a m := by
  intro m
  induction m with
  | zero => intro _; exact Nat.one_pos
  | succ m ih =>
      intro ha
      show 0 < seqProd a m * a m
      exact Nat.mul_pos (ih fun i hi => ha i (by omega)) (ha m (by omega))

/-- **Multiplicative telescope.**  For step sequences (`2^{kᵢ}·a_{i+1} = 3aᵢ + 1`):
`2^{A_m} · Π_{i<m} a_{i+1} = Π_{i<m} (3aᵢ + 1)`. -/
theorem cycle_mul_telescope (a k : ℕ → ℕ)
    (hstep : ∀ i, 2 ^ (k i) * a (i + 1) = 3 * a i + 1) :
    ∀ m, 2 ^ (partialA k m) * seqProd (fun i => a (i + 1)) m
      = seqProd (fun i => 3 * a i + 1) m := by
  intro m
  induction m with
  | zero => simp [partialA, seqProd]
  | succ m ih =>
      show 2 ^ (partialA k m + k m) * (seqProd (fun i => a (i + 1)) m * a (m + 1))
        = seqProd (fun i => 3 * a i + 1) m * (3 * a m + 1)
      rw [pow_add, ← hstep m, ← ih]
      ring

/-- Cyclic shift of the running product: `(Π_{i<m} a_{i+1}) · a₀ = (Π_{i<m} aᵢ) · a_m`. -/
theorem seqProd_shift (a : ℕ → ℕ) :
    ∀ m, seqProd (fun i => a (i + 1)) m * a 0 = seqProd a m * a m := by
  intro m
  induction m with
  | zero => simp [seqProd]
  | succ m ih =>
      show (seqProd (fun i => a (i + 1)) m * a (m + 1)) * a 0
        = (seqProd a m * a m) * a (m + 1)
      calc (seqProd (fun i => a (i + 1)) m * a (m + 1)) * a 0
          = (seqProd (fun i => a (i + 1)) m * a 0) * a (m + 1) := by ring
        _ = (seqProd a m * a m) * a (m + 1) := by rw [ih]

/-- `Π_{i<m} (3aᵢ+1) ≤ 4^m · Π_{i<m} aᵢ` for sequences positive below `m`. -/
theorem seqProd_le_four_pow (a : ℕ → ℕ) :
    ∀ m, (∀ i, i < m → 1 ≤ a i) →
      seqProd (fun i => 3 * a i + 1) m ≤ 4 ^ m * seqProd a m := by
  intro m
  induction m with
  | zero => intro _; simp [seqProd]
  | succ m ih =>
      intro ha
      have h1 := ih fun i hi => ha i (by omega)
      have h2 : 3 * a m + 1 ≤ 4 * a m := by have := ha m (by omega); omega
      show seqProd (fun i => 3 * a i + 1) m * (3 * a m + 1)
        ≤ 4 ^ (m + 1) * (seqProd a m * a m)
      calc seqProd (fun i => 3 * a i + 1) m * (3 * a m + 1)
          ≤ (4 ^ m * seqProd a m) * (4 * a m) := Nat.mul_le_mul h1 h2
        _ = 4 ^ (m + 1) * (seqProd a m * a m) := by rw [pow_succ]; ring

/-- Strict version: if all entries below `m ≥ 1` are `≥ 2`, then
`Π_{i<m} (3aᵢ+1) < 4^m · Π_{i<m} aᵢ`. -/
theorem seqProd_lt_four_pow (a : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (ha : ∀ i, i < m → 2 ≤ a i) :
    seqProd (fun i => 3 * a i + 1) m < 4 ^ m * seqProd a m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hle : seqProd (fun i => 3 * a i + 1) m' ≤ 4 ^ m' * seqProd a m' :=
    seqProd_le_four_pow a m' fun i hi => by have := ha i (by omega); omega
  have hpos : 0 < 4 ^ m' * seqProd a m' := by
    have hP : 0 < seqProd a m' := seqProd_pos a m' fun i hi => by
      have := ha i (by omega); omega
    positivity
  have hlast : 3 * a m' + 1 < 4 * a m' := by have := ha m' (by omega); omega
  show seqProd (fun i => 3 * a i + 1) m' * (3 * a m' + 1)
    < 4 ^ (m' + 1) * (seqProd a m' * a m')
  calc seqProd (fun i => 3 * a i + 1) m' * (3 * a m' + 1)
      ≤ (4 ^ m' * seqProd a m') * (3 * a m' + 1) := Nat.mul_le_mul_right _ hle
    _ < (4 ^ m' * seqProd a m') * (4 * a m') := mul_lt_mul_of_pos_left hlast hpos
    _ = 4 ^ (m' + 1) * (seqProd a m' * a m') := by rw [pow_succ]; ring

/-- `Syr` output is always positive. -/
theorem Syr_pos (n : ℕ) : 0 < Syr n := by
  have h := Syr_step n
  by_contra h0
  push_neg at h0
  have hz : Syr n = 0 := by omega
  rw [hz, Nat.mul_zero] at h
  omega

/-- Iterates of a positive start stay positive. -/
theorem syr_iterate_pos (a0 : ℕ) (ha : 0 < a0) (i : ℕ) : 0 < (Syr^[i]) a0 := by
  cases i with
  | zero => exact ha
  | succ i => rw [Function.iterate_succ_apply']; exact Syr_pos _

/-- `1` is a fixed point of `Syr`. -/
theorem Syr_one : Syr 1 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hs := Syr_step 1
  norm_num [h4] at hs
  omega

theorem syr_iterate_one (k : ℕ) : (Syr^[k]) 1 = 1 :=
  Function.iterate_fixed Syr_one k

/-- **Multiplicative cycle equation.**  A positive `m`-periodic point of `Syr` satisfies
`2^{A_m} · Π_{i<m} aᵢ = Π_{i<m} (3aᵢ + 1)`, where `aᵢ = Syr^[i] a₀`. -/
theorem syr_cycle_mul_equation (a0 m : ℕ) (ha : 0 < a0) (h : (Syr^[m]) a0 = a0) :
    2 ^ cycleA a0 m * seqProd (fun i => (Syr^[i]) a0) m
      = seqProd (fun i => 3 * (Syr^[i]) a0 + 1) m := by
  have hstep : ∀ i, 2 ^ (cycleK a0 i) * (Syr^[i + 1]) a0 = 3 * (Syr^[i]) a0 + 1 := by
    intro i
    rw [Function.iterate_succ_apply']
    exact Syr_step ((Syr^[i]) a0)
  have htel : 2 ^ cycleA a0 m * seqProd (fun i => (Syr^[i + 1]) a0) m
      = seqProd (fun i => 3 * (Syr^[i]) a0 + 1) m :=
    cycle_mul_telescope (fun i => (Syr^[i]) a0) (cycleK a0) hstep m
  have hshift : seqProd (fun i => (Syr^[i + 1]) a0) m * (Syr^[0]) a0
      = seqProd (fun i => (Syr^[i]) a0) m * (Syr^[m]) a0 :=
    seqProd_shift (fun i => (Syr^[i]) a0) m
  have key : seqProd (fun i => 3 * (Syr^[i]) a0 + 1) m * a0
      = 2 ^ cycleA a0 m * seqProd (fun i => (Syr^[i]) a0) m * a0 := by
    calc seqProd (fun i => 3 * (Syr^[i]) a0 + 1) m * a0
        = (2 ^ cycleA a0 m * seqProd (fun i => (Syr^[i + 1]) a0) m) * a0 := by
          rw [← htel]
      _ = 2 ^ cycleA a0 m * (seqProd (fun i => (Syr^[i + 1]) a0) m * (Syr^[0]) a0) := by
          show (2 ^ cycleA a0 m * seqProd (fun i => (Syr^[i + 1]) a0) m) * a0
            = 2 ^ cycleA a0 m * (seqProd (fun i => (Syr^[i + 1]) a0) m * a0)
          ring
      _ = 2 ^ cycleA a0 m * (seqProd (fun i => (Syr^[i]) a0) m * (Syr^[m]) a0) := by
          rw [hshift]
      _ = 2 ^ cycleA a0 m * seqProd (fun i => (Syr^[i]) a0) m * a0 := by
          rw [h]; ring
  exact (Nat.eq_of_mul_eq_mul_right ha key).symm

/-- **Upper corridor (uniform in `m`).**  Every positive `m`-cycle of `Syr` has
`A_m ≤ 2m`. -/
theorem syr_cycle_A_le_two_mul (a0 m : ℕ) (ha : 0 < a0) (h : (Syr^[m]) a0 = a0) :
    cycleA a0 m ≤ 2 * m := by
  have hposall : ∀ i, i < m → 1 ≤ (Syr^[i]) a0 := fun i _ => syr_iterate_pos a0 ha i
  have hP : 0 < seqProd (fun i => (Syr^[i]) a0) m :=
    seqProd_pos (fun i => (Syr^[i]) a0) m hposall
  have hmul := syr_cycle_mul_equation a0 m ha h
  have hle := seqProd_le_four_pow (fun i => (Syr^[i]) a0) m hposall
  have h2A : seqProd (fun i => (Syr^[i]) a0) m * 2 ^ cycleA a0 m
      ≤ seqProd (fun i => (Syr^[i]) a0) m * 4 ^ m := by
    rw [Nat.mul_comm (seqProd (fun i => (Syr^[i]) a0) m) (2 ^ cycleA a0 m),
        Nat.mul_comm (seqProd (fun i => (Syr^[i]) a0) m) (4 ^ m), hmul]
    exact hle
  have h2 : (2 : ℕ) ^ cycleA a0 m ≤ 4 ^ m := Nat.le_of_mul_le_mul_left h2A hP
  have h4 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4] at h2
  by_contra hgt
  push_neg at hgt
  have hmono : (2 : ℕ) ^ (2 * m + 1) ≤ 2 ^ cycleA a0 m :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hps : (2 : ℕ) ^ (2 * m + 1) = 2 ^ (2 * m) * 2 := pow_succ 2 (2 * m)
  have hpp : 0 < (2 : ℕ) ^ (2 * m) := pow_pos (by norm_num) _
  omega

/-- **Strict upper corridor for nontrivial cycles (S240).**  A nontrivial (`a₀ ≥ 2`)
`m`-cycle (`m ≥ 1`) has `A_m < 2m`. -/
theorem syr_cycle_A_lt_two_mul (a0 m : ℕ) (ha : 2 ≤ a0) (hm : 0 < m)
    (h : (Syr^[m]) a0 = a0) :
    cycleA a0 m < 2 * m := by
  have helem : ∀ i, i < m → 2 ≤ (Syr^[i]) a0 := by
    intro i him
    have hpos : 0 < (Syr^[i]) a0 := syr_iterate_pos a0 (by omega) i
    by_contra hlt
    push_neg at hlt
    have h1 : (Syr^[i]) a0 = 1 := by omega
    have hmi : m - i + i = m := by omega
    have hsplit : (Syr^[m]) a0 = (Syr^[m - i]) ((Syr^[i]) a0) := by
      calc (Syr^[m]) a0 = (Syr^[m - i + i]) a0 := by rw [hmi]
        _ = (Syr^[m - i]) ((Syr^[i]) a0) := Function.iterate_add_apply Syr (m - i) i a0
    rw [h1, syr_iterate_one] at hsplit
    omega
  have hP : 0 < seqProd (fun i => (Syr^[i]) a0) m :=
    seqProd_pos (fun i => (Syr^[i]) a0) m
      fun i hi => Nat.lt_of_lt_of_le (by norm_num) (helem i hi)
  have hmul := syr_cycle_mul_equation a0 m (by omega) h
  have hlt := seqProd_lt_four_pow (fun i => (Syr^[i]) a0) m hm helem
  have h2A : seqProd (fun i => (Syr^[i]) a0) m * 2 ^ cycleA a0 m
      < seqProd (fun i => (Syr^[i]) a0) m * 4 ^ m := by
    rw [Nat.mul_comm (seqProd (fun i => (Syr^[i]) a0) m) (2 ^ cycleA a0 m),
        Nat.mul_comm (seqProd (fun i => (Syr^[i]) a0) m) (4 ^ m), hmul]
    exact hlt
  have h2 : (2 : ℕ) ^ cycleA a0 m < 4 ^ m := Nat.lt_of_mul_lt_mul_left h2A
  have h4 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4] at h2
  by_contra hge
  push_neg at hge
  have hmono : (2 : ℕ) ^ (2 * m) ≤ 2 ^ cycleA a0 m :=
    Nat.pow_le_pow_right (by norm_num) hge
  omega

/-- **The window theorem (S240).**  The exponent of a NONTRIVIAL Syracuse cycle is
trapped in the corridor window: `3^m < 2^{A_m}` and `A_m < 2m`. -/
theorem syr_cycle_window (a0 m : ℕ) (ha : 2 ≤ a0) (hm : 0 < m)
    (h : (Syr^[m]) a0 = a0) :
    3 ^ m < 2 ^ cycleA a0 m ∧ cycleA a0 m < 2 * m :=
  ⟨syr_cycle_corridor' a0 m hm h, syr_cycle_A_lt_two_mul a0 m ha hm h⟩

/-! ### Step 2 — the verification-frontier coupling

The engine of the modern cycle bounds (Eliahou 1993 → Simons–de Weger 2005 → Hercher 2022):
a nontrivial cycle's elements all exceed the computational verification frontier `X₀`,
because a cycle element is a periodic point, and a periodic point whose orbit reaches `1`
IS `1`.  We take the verification fact as an EXPLICIT HYPOTHESIS (`SyrVerifiedUpTo X₀`) —
stated, never asserted.  (Real-world instance: Collatz convergence is verified for all
`n ≤ 704·2⁶⁰ ≈ 8.1·10²⁰`, Barina, *J. Supercomputing* 2020; bridging that statement about
the full Collatz map to `SyrVerifiedUpTo` for the accelerated odd map is an elementary but
separate step, not done here.)

Combined with step 1's gap identity `(2^{A_m} − 3^m)·a₀ = C_m`, the frontier forces the
QUANTITATIVE bound `(2^{A_m} − 3^m)·X₀ < C_m` — the input the continued-fraction step
(step 3) consumes. -/

/-- `n` reaches the fixed point `1` under the Syracuse iteration. -/
def SyrReaches1 (n : ℕ) : Prop := ∃ k, (Syr^[k]) n = 1

/-- The computational verification hypothesis: every positive `n ≤ X₀` reaches `1`.
STATED as an explicit hypothesis, never asserted. -/
def SyrVerifiedUpTo (X₀ : ℕ) : Prop := ∀ n, 0 < n → n ≤ X₀ → SyrReaches1 n

/-- A periodic point is fixed by every multiple of its period. -/
theorem syr_periodic_mul (a m : ℕ) (h : (Syr^[m]) a = a) :
    ∀ q, (Syr^[q * m]) a = a := by
  intro q
  induction q with
  | zero => rw [Nat.zero_mul]; rfl
  | succ q ih =>
      have hadd : (q + 1) * m = m + q * m := by ring
      rw [hadd, Function.iterate_add_apply, ih, h]

/-- **A periodic point that reaches `1` is `1`.**  Reduce the hitting time mod the period,
then close the cycle through the fixed point `1`. -/
theorem syr_periodic_eq_one_of_reaches (a m : ℕ) (hm : 0 < m)
    (h : (Syr^[m]) a = a) (hr : SyrReaches1 a) : a = 1 := by
  obtain ⟨k, hk⟩ := hr
  have hper : (Syr^[k / m * m]) a = a := syr_periodic_mul a m h (k / m)
  have hred : (Syr^[k % m]) a = 1 := by
    have h1 : (Syr^[k % m + k / m * m]) a = (Syr^[k % m]) ((Syr^[k / m * m]) a) :=
      Function.iterate_add_apply Syr (k % m) (k / m * m) a
    rw [hper, Nat.mod_add_div'] at h1
    rw [← h1]
    exact hk
  have hrm : k % m < m := Nat.mod_lt k hm
  calc a = (Syr^[m]) a := h.symm
    _ = (Syr^[(m - k % m) + k % m]) a := by rw [Nat.sub_add_cancel (le_of_lt hrm)]
    _ = (Syr^[m - k % m]) ((Syr^[k % m]) a) :=
        Function.iterate_add_apply Syr (m - k % m) (k % m) a
    _ = (Syr^[m - k % m]) 1 := by rw [hred]
    _ = 1 := syr_iterate_one _

/-- **Every element of a nontrivial cycle exceeds the verification frontier.**  Each
`Syr^[i] a` is itself a periodic point; were it `≤ X₀`, the verification hypothesis would
make it reach `1`, forcing it — and then `a` itself — to equal `1`. -/
theorem syr_cycle_elements_above_frontier {X₀ : ℕ} (hver : SyrVerifiedUpTo X₀)
    {a m : ℕ} (ha : 0 < a) (hm : 0 < m) (h : (Syr^[m]) a = a) (hne : a ≠ 1) :
    ∀ i, X₀ < (Syr^[i]) a := by
  intro i
  by_contra hle
  push_neg at hle
  have hbpos : 0 < (Syr^[i]) a := syr_iterate_pos a ha i
  have hbper : (Syr^[m]) ((Syr^[i]) a) = (Syr^[i]) a := by
    calc (Syr^[m]) ((Syr^[i]) a)
        = (Syr^[m + i]) a := (Function.iterate_add_apply Syr m i a).symm
      _ = (Syr^[i + m]) a := by rw [Nat.add_comm]
      _ = (Syr^[i]) ((Syr^[m]) a) := Function.iterate_add_apply Syr i m a
      _ = (Syr^[i]) a := by rw [h]
  have hb1 : (Syr^[i]) a = 1 :=
    syr_periodic_eq_one_of_reaches _ m hm hbper (hver _ hbpos hle)
  exact hne (syr_periodic_eq_one_of_reaches a m hm h ⟨i, hb1⟩)

/-- **The quantitative frontier bound (step 1 ⊗ step 2).**  For a nontrivial cycle,
`(2^{A_m} − 3^m) · X₀ < C_m` — the gap times the verification frontier is beaten by the
cycle constant.  This is the exact input of the continued-fraction step. -/
theorem syr_cycle_gap_mul_frontier_lt {X₀ : ℕ} (hver : SyrVerifiedUpTo X₀)
    {a0 m : ℕ} (ha : 0 < a0) (hm : 0 < m) (h : (Syr^[m]) a0 = a0) (hne : a0 ≠ 1) :
    (2 ^ cycleA a0 m - 3 ^ m) * X₀ < cycleCm a0 m := by
  have hX0 : X₀ < a0 := by
    have h0 := syr_cycle_elements_above_frontier hver ha hm h hne 0
    exact h0
  have hgap : 0 < 2 ^ cycleA a0 m - 3 ^ m := syr_cycle_gap_pos a0 m hm h
  calc (2 ^ cycleA a0 m - 3 ^ m) * X₀
      < (2 ^ cycleA a0 m - 3 ^ m) * a0 := mul_lt_mul_of_pos_left hX0 hgap
    _ = cycleCm a0 m := syr_cycle_gap_eq a0 m h

/-! ### Step 3 — the continued-fraction (mediant) exclusion, fully integer-arithmetic

The Lean image of the Hercher-style ratchet, with NO real logarithms anywhere:

  * the multiplicative cycle equation + the frontier give the SANDWICH
    `3^m < 2^{A_m}` and `2^{A_m}·V^m ≤ 3^m·(V+1)^m` with `V := 3X₀`
    (per-factor: `(3aᵢ+1)·V ≤ 3aᵢ·(V+1) ⟺ X₀ ≤ aᵢ`);
  * a CONSECUTIVE CONVERGENT PAIR `L/Λ < log₂3 < U/Υ` of the continued fraction of
    `log₂3` enters as three INTEGER certificates: unimodularity `U·Λ = L·Υ + 1`, the
    lower side `2^L < 3^Λ`, and the quality bound `3^Υ·(V+1)^Υ < 2^U·V^Υ`;
  * the sandwich forces `L/Λ < A/m < U/Υ` (pure power-comparison juggling), and the
    UNIMODULAR MEDIANT IDENTITY `m = Λ·(Um − AΥ) + Υ·(AΛ − Lm)` forces `m ≥ Λ + Υ`.

Concrete instances below: the pair `84/53 < log₂3 < 485/306` (M₀ = 359, X₀ = 2²⁰) and
`1054/665 < log₂3 < 24727/15601` (M₀ = 16266, X₀ = 2²⁹).  Both X₀ are far below the
verified frontier of the literature (`704·2⁶⁰`, Barina 2020), but `SyrVerifiedUpTo X₀`
remains an EXPLICIT HYPOTHESIS throughout — stated, never asserted. -/

/-- Distributing a constant through the running product: `Π (c·aᵢ) = c^m · Π aᵢ`. -/
theorem seqProd_const_mul (c : ℕ) (a : ℕ → ℕ) :
    ∀ m, seqProd (fun i => c * a i) m = c ^ m * seqProd a m := by
  intro m
  induction m with
  | zero => simp [seqProd]
  | succ m ih =>
      show seqProd (fun i => c * a i) m * (c * a m) = c ^ (m + 1) * (seqProd a m * a m)
      rw [ih, pow_succ]
      ring

/-- **The frontier product bound.**  If every `3aᵢ ≥ V` below `m`, then
`Π(3aᵢ+1) · V^m ≤ Π(3aᵢ) · (V+1)^m` (per-factor: `(3a+1)V ≤ 3a(V+1) ⟺ V ≤ 3a`). -/
theorem seqProd_frontier_le (a : ℕ → ℕ) (V : ℕ) :
    ∀ m, (∀ i, i < m → V ≤ 3 * a i) →
      seqProd (fun i => 3 * a i + 1) m * V ^ m
        ≤ seqProd (fun i => 3 * a i) m * (V + 1) ^ m := by
  intro m
  induction m with
  | zero => intro _; simp [seqProd]
  | succ m ih =>
      intro hV
      have h1 := ih fun i hi => hV i (by omega)
      have h2 : (3 * a m + 1) * V ≤ 3 * a m * (V + 1) := by
        have := hV m (by omega)
        nlinarith
      show seqProd (fun i => 3 * a i + 1) m * (3 * a m + 1) * V ^ (m + 1)
        ≤ seqProd (fun i => 3 * a i) m * (3 * a m) * (V + 1) ^ (m + 1)
      calc seqProd (fun i => 3 * a i + 1) m * (3 * a m + 1) * V ^ (m + 1)
          = (seqProd (fun i => 3 * a i + 1) m * V ^ m) * ((3 * a m + 1) * V) := by
            rw [pow_succ]; ring
        _ ≤ (seqProd (fun i => 3 * a i) m * (V + 1) ^ m) * (3 * a m * (V + 1)) :=
            Nat.mul_le_mul h1 h2
        _ = seqProd (fun i => 3 * a i) m * (3 * a m) * (V + 1) ^ (m + 1) := by
            rw [pow_succ]; ring

/-- **The frontier sandwich (upper side).**  A nontrivial cycle above the frontier `X₀`
satisfies `2^{A_m} · (3X₀)^m ≤ 3^m · (3X₀+1)^m`. -/
theorem syr_cycle_frontier_sandwich {X₀ : ℕ} (hver : SyrVerifiedUpTo X₀)
    {a0 m : ℕ} (ha : 0 < a0) (hm : 0 < m) (h : (Syr^[m]) a0 = a0) (hne : a0 ≠ 1) :
    2 ^ cycleA a0 m * (3 * X₀) ^ m ≤ 3 ^ m * (3 * X₀ + 1) ^ m := by
  have helem := syr_cycle_elements_above_frontier hver ha hm h hne
  have hV : ∀ i, i < m → 3 * X₀ ≤ 3 * (Syr^[i]) a0 := fun i _ =>
    Nat.mul_le_mul (le_refl 3) (le_of_lt (helem i))
  have hP : 0 < seqProd (fun i => (Syr^[i]) a0) m :=
    seqProd_pos (fun i => (Syr^[i]) a0) m (fun i _ => syr_iterate_pos a0 ha i)
  have hmul := syr_cycle_mul_equation a0 m ha h
  have hfront := seqProd_frontier_le (fun i => (Syr^[i]) a0) (3 * X₀) m hV
  have hconst : seqProd (fun i => 3 * (Syr^[i]) a0) m
      = 3 ^ m * seqProd (fun i => (Syr^[i]) a0) m :=
    seqProd_const_mul 3 (fun i => (Syr^[i]) a0) m
  have hre : seqProd (fun i => (Syr^[i]) a0) m * (2 ^ cycleA a0 m * (3 * X₀) ^ m)
      ≤ seqProd (fun i => (Syr^[i]) a0) m * (3 ^ m * (3 * X₀ + 1) ^ m) := by
    calc seqProd (fun i => (Syr^[i]) a0) m * (2 ^ cycleA a0 m * (3 * X₀) ^ m)
        = (2 ^ cycleA a0 m * seqProd (fun i => (Syr^[i]) a0) m) * (3 * X₀) ^ m := by
          ring
      _ = seqProd (fun i => 3 * (Syr^[i]) a0 + 1) m * (3 * X₀) ^ m := by rw [hmul]
      _ ≤ seqProd (fun i => 3 * (Syr^[i]) a0) m * (3 * X₀ + 1) ^ m := hfront
      _ = seqProd (fun i => (Syr^[i]) a0) m * (3 ^ m * (3 * X₀ + 1) ^ m) := by
          rw [hconst]; ring
  exact Nat.le_of_mul_le_mul_left hre hP

/-- **The unimodular mediant bound (pure ℕ).**  If `U·Λ = L·Υ + 1` and the fraction
`A/m` lies strictly between `L/Λ` and `U/Υ` (`Lm < AΛ`, `AΥ < Um`), then `m ≥ Λ + Υ` —
the mediant identity `m = Λ·(Um − AΥ) + Υ·(AΛ − Lm)`. -/
theorem mediant_period_bound {L Λ U Υ A m : ℕ}
    (huni : U * Λ = L * Υ + 1)
    (h1 : L * m < A * Λ) (h2 : A * Υ < U * m) :
    Λ + Υ ≤ m := by
  have e1 : Λ * (A * Υ) + Λ ≤ Λ * (U * m) := by
    have h2' : A * Υ + 1 ≤ U * m := h2
    calc Λ * (A * Υ) + Λ = Λ * (A * Υ + 1) := by ring
      _ ≤ Λ * (U * m) := Nat.mul_le_mul (le_refl Λ) h2'
  have e2 : Υ * (L * m) + Υ ≤ Υ * (A * Λ) := by
    have h1' : L * m + 1 ≤ A * Λ := h1
    calc Υ * (L * m) + Υ = Υ * (L * m + 1) := by ring
      _ ≤ Υ * (A * Λ) := Nat.mul_le_mul (le_refl Υ) h1'
  have e3 : Λ * (U * m) = Υ * (L * m) + m := by
    calc Λ * (U * m) = (U * Λ) * m := by ring
      _ = (L * Υ + 1) * m := by rw [huni]
      _ = Υ * (L * m) + m := by ring
  have e4 : Λ * (A * Υ) = Υ * (A * Λ) := by ring
  omega

/-- Conditional cycle exclusion below a period bound (the step-3 deliverable shape). -/
def NoSyrCycleBelowPeriod (M₀ : ℕ) : Prop :=
  ∀ a m : ℕ, 0 < a → 0 < m → m < M₀ → (Syr^[m]) a = a → a = 1

/-- **Step 3 (the mediant exclusion).**  Given the verification hypothesis up to `X₀`
and a consecutive convergent pair `L/Λ < log₂3 < U/Υ` certified by three INTEGER facts —
unimodularity, the lower side `2^L < 3^Λ`, and the quality bound
`3^Υ·(3X₀+1)^Υ < 2^U·(3X₀)^Υ` — every nontrivial Syracuse cycle has period `≥ Λ + Υ`. -/
theorem syr_mediant_exclusion {X₀ L Λ U Υ : ℕ}
    (hver : SyrVerifiedUpTo X₀) (hΛ : 0 < Λ) (hΥ : 0 < Υ)
    (huni : U * Λ = L * Υ + 1)
    (hlow : 2 ^ L < 3 ^ Λ)
    (hcert : 3 ^ Υ * (3 * X₀ + 1) ^ Υ < 2 ^ U * (3 * X₀) ^ Υ) :
    NoSyrCycleBelowPeriod (Λ + Υ) := by
  intro a m ha hm hmlt hcyc
  by_contra hne
  have hcorr : 3 ^ m < 2 ^ cycleA a m := syr_cycle_corridor' a m hm hcyc
  -- lower side: L/Λ < A/m, i.e. L·m < A·Λ
  have hAL : L * m < cycleA a m * Λ := by
    by_contra hle
    push_neg at hle
    have h1 : (3 : ℕ) ^ (m * Λ) < 2 ^ (cycleA a m * Λ) := by
      have h0 : ((3 : ℕ) ^ m) ^ Λ < ((2 : ℕ) ^ cycleA a m) ^ Λ :=
        Nat.pow_lt_pow_left hcorr (by omega)
      calc (3 : ℕ) ^ (m * Λ) = ((3 : ℕ) ^ m) ^ Λ := by rw [pow_mul]
        _ < ((2 : ℕ) ^ cycleA a m) ^ Λ := h0
        _ = 2 ^ (cycleA a m * Λ) := by rw [pow_mul]
    have h2 : (2 : ℕ) ^ (L * m) < 3 ^ (Λ * m) := by
      have h0 : ((2 : ℕ) ^ L) ^ m < ((3 : ℕ) ^ Λ) ^ m :=
        Nat.pow_lt_pow_left hlow (by omega)
      calc (2 : ℕ) ^ (L * m) = ((2 : ℕ) ^ L) ^ m := by rw [pow_mul]
        _ < ((3 : ℕ) ^ Λ) ^ m := h0
        _ = 3 ^ (Λ * m) := by rw [pow_mul]
    have h3 : (2 : ℕ) ^ (cycleA a m * Λ) ≤ 2 ^ (L * m) :=
      Nat.pow_le_pow_right (by norm_num) hle
    have hc : (3 : ℕ) ^ (Λ * m) = 3 ^ (m * Λ) := by rw [Nat.mul_comm]
    omega
  -- upper side: A/m < U/Υ, i.e. A·Υ < U·m
  have hAU : cycleA a m * Υ < U * m := by
    by_contra hge
    push_neg at hge
    have hs := syr_cycle_frontier_sandwich hver ha hm hcyc hne
    have hsΥ : (2 ^ cycleA a m * (3 * X₀) ^ m) ^ Υ
        ≤ (3 ^ m * (3 * X₀ + 1) ^ m) ^ Υ := Nat.pow_le_pow_left hs Υ
    have e1 : ((2 : ℕ) ^ U * (3 * X₀) ^ Υ) ^ m = 2 ^ (U * m) * (3 * X₀) ^ (Υ * m) := by
      ring
    have e2 : ((2 : ℕ) ^ cycleA a m * (3 * X₀) ^ m) ^ Υ
        = 2 ^ (cycleA a m * Υ) * (3 * X₀) ^ (Υ * m) := by
      ring
    have e3 : ((3 : ℕ) ^ m * (3 * X₀ + 1) ^ m) ^ Υ
        = ((3 : ℕ) ^ Υ * (3 * X₀ + 1) ^ Υ) ^ m := by
      ring
    have hpow : (2 : ℕ) ^ (U * m) ≤ 2 ^ (cycleA a m * Υ) :=
      Nat.pow_le_pow_right (by norm_num) hge
    have hfin : ((2 : ℕ) ^ U * (3 * X₀) ^ Υ) ^ m
        ≤ ((3 : ℕ) ^ Υ * (3 * X₀ + 1) ^ Υ) ^ m := by
      calc ((2 : ℕ) ^ U * (3 * X₀) ^ Υ) ^ m
          = 2 ^ (U * m) * (3 * X₀) ^ (Υ * m) := e1
        _ ≤ 2 ^ (cycleA a m * Υ) * (3 * X₀) ^ (Υ * m) :=
            Nat.mul_le_mul hpow (le_refl _)
        _ = ((2 : ℕ) ^ cycleA a m * (3 * X₀) ^ m) ^ Υ := e2.symm
        _ ≤ (3 ^ m * (3 * X₀ + 1) ^ m) ^ Υ := hsΥ
        _ = ((3 : ℕ) ^ Υ * (3 * X₀ + 1) ^ Υ) ^ m := e3
    have hroot : (2 : ℕ) ^ U * (3 * X₀) ^ Υ ≤ 3 ^ Υ * (3 * X₀ + 1) ^ Υ := by
      by_contra hgt
      push_neg at hgt
      have := Nat.pow_lt_pow_left hgt (n := m) (by omega)
      omega
    omega
  have := mediant_period_bound huni hAL hAU
  omega

/-- **Concrete instance, convergent pair `84/53 < log₂3 < 485/306`** (unimodular:
`485·53 = 84·306 + 1`): conditional on verification up to `2²⁰ ≈ 10⁶`, no nontrivial
Syracuse cycle of period below `359`. -/
theorem syr_no_cycle_below_359 (hver : SyrVerifiedUpTo (2 ^ 20)) :
    NoSyrCycleBelowPeriod 359 := by
  have h := syr_mediant_exclusion (L := 84) (Λ := 53) (U := 485) (Υ := 306) hver
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)
  simpa using h

/- LARGER INSTANCES (honest scope note).  The next consecutive pair
`1054/665 < log₂3 < 24727/15601` (unimodular: `24727·665 = 1054·15601 + 1`, certificates
verified numerically) would give `NoSyrCycleBelowPeriod 16266` from `SyrVerifiedUpTo 2²⁹`.
The mathematics is identical; the blocker is purely technical: `decide`'s elaborator-side
reduction unfolds `Nat.pow` UNARILY, so exponent `15601` exceeds any sane `maxRecDepth`
(the kernel's GMP arithmetic itself would be fast).  A pow-by-squaring certificate helper
(staging `x^{2k} = (x^k)^2` as explicit lemmas) would unlock arbitrary convergent pairs;
deferred. -/

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
