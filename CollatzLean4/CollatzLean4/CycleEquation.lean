/-
Copyright (c) 2026 Benet Andújar Guardado.

S239 — Cycle direction (NEW line): the affine identity as the Collatz cycle
equation, with HONEST scope marking.

Context. Collatz = (no nontrivial cycles) + (no divergent orbits). The whole
prior development attacks DIVERGENCE (slope/descent barriers). Cycles are the
other, algebraically rigid half. This file opens the cycle line.

§1  Accumulator refutation + corridor.  The inverse accumulator `(n,A,q,B)` with
    `GoodState : 3^q·n + B = 2^A` normalizes the tree at the ROOT (n=1). The
    naive rearrangement `n·(2^A − 3^q) = B` holds IFF n = 1
    (`cycle_rearrangement_iff_n_one`) — so nontrivial cycles need the GENERAL
    equation, not that rearrangement.

§2  Forward Syracuse cycle equation (self-contained, grounded in real Collatz).
    `Syr n = (3n+1)/2^{ν₂(3n+1)}`; an `m`-cycle satisfies, by telescoping the
    per-step identities, the exact equation
        2^A · a = 3^m · a + C,     C = Σ_{i<m} 3^{m-1-i} 2^{A_i}  > 0,
    hence the strict corridor `3^m < 2^A`.  `syr_cycle_equation` derives this
    for any genuine periodic point of `Syr`.

Open frontier (Baker).  The UNCONDITIONAL "no nontrivial cycles"
(`NoNontrivialSyrCycle`) needs an effective lower bound on |2^A − 3^m| (linear
forms in logarithms, Baker/Matveev), ABSENT from Mathlib. Stated, never assumed.
0 sorry / 0 ad-hoc axiom in this file.
-/

import CollatzLean4.Defect
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace CollatzLean4.Admissible

/-! ## §1 — Accumulator: refutation of the naive rearrangement + corridor -/

/-- **Refutation of the naive cycle rearrangement.**
`n·(2^A − 3^q) = B` extracted from `GoodState` holds **iff `n = 1`**: since
`GoodState` gives `B = 2^A − 3^q·n`, the rearrangement is equivalent to
`(n − 1)·2^A = 0`. The accumulator natively encodes only the root/trivial cycle. -/
theorem cycle_rearrangement_iff_n_one (s : AdmState) (h : GoodState s) :
    ((s.n : Int) * ((2 : Int) ^ s.A - (3 : Int) ^ s.q) = (s.B : Int))
      ↔ s.n = 1 := by
  have hI : (3 : Int) ^ s.q * (s.n : Int) + (s.B : Int) = (2 : Int) ^ s.A := by
    have hh := h; unfold GoodState at hh; exact_mod_cast hh
  have identity :
      (s.n : Int) * ((2 : Int) ^ s.A - (3 : Int) ^ s.q) - (s.B : Int)
        = ((s.n : Int) - 1) * (2 : Int) ^ s.A := by
    have hB : (s.B : Int) = (2 : Int) ^ s.A - (3 : Int) ^ s.q * (s.n : Int) := by
      linarith
    rw [hB]; ring
  have h2 : (2 : Int) ^ s.A ≠ 0 := by positivity
  constructor
  · intro hcyc
    have hzero : ((s.n : Int) - 1) * (2 : Int) ^ s.A = 0 := by
      rw [← identity]; linarith
    have hn0 : (s.n : Int) - 1 = 0 := by
      rcases mul_eq_zero.mp hzero with h' | h'
      · exact h'
      · exact absurd h' h2
    have hn1 : (s.n : Int) = 1 := by linarith
    exact_mod_cast hn1
  · intro hn1
    have hn1I : (s.n : Int) = 1 := by exact_mod_cast hn1
    have hzero : ((s.n : Int) - 1) * (2 : Int) ^ s.A = 0 := by rw [hn1I]; ring
    have hcyc :
        (s.n : Int) * ((2 : Int) ^ s.A - (3 : Int) ^ s.q) - (s.B : Int) = 0 := by
      rw [identity]; exact hzero
    linarith

/-- **Accumulator corridor (Baker-free).** Every admissible state satisfies
`Nat.log 2 (3^q) ≤ A`, sharper than the prior `q ≤ A`. -/
theorem cycle_corridor (s : AdmState) (h : Inv s) :
    Nat.log 2 (3 ^ s.q) ≤ s.A := by
  have hle : 3 ^ s.q ≤ 2 ^ s.A := three_pow_q_le_two_pow_A s h
  calc Nat.log 2 (3 ^ s.q)
      ≤ Nat.log 2 (2 ^ s.A) := Nat.log_mono_right hle
    _ = s.A := Nat.log_pow (show (1 : ℕ) < 2 by norm_num) s.A

/-- Corollary along admissible runs. -/
theorem evalWord_cycle_corridor (w : Word) :
    Nat.log 2 (3 ^ (evalWord w).q) ≤ (evalWord w).A :=
  cycle_corridor _ (runWord_preserves_inv w init_inv)

/-! ## §2 — Forward Syracuse cycle equation (grounded in real Collatz) -/

/-- Forward accelerated Syracuse map on odds: `Syr n = (3n+1)/2^{ν₂(3n+1)}`.
Fixed point: `Syr 1 = 4/4 = 1`. -/
def Syr (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ (padicValNat 2 (3 * n + 1))

/-- The exact one-step identity: `2^{ν₂(3a+1)} · Syr a = 3a + 1`. -/
theorem Syr_step (a : ℕ) :
    2 ^ (padicValNat 2 (3 * a + 1)) * Syr a = 3 * a + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Syr
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

/-- Partial 2-adic exponent `A_m = k_0 + ⋯ + k_{m-1}`. -/
def partialA (k : ℕ → ℕ) : ℕ → ℕ
  | 0       => 0
  | (m + 1) => partialA k m + k m

/-- Cycle constant `C_m = Σ_{i<m} 3^{m-1-i} 2^{A_i}`, via `C_{m+1} = 3 C_m + 2^{A_m}`. -/
def cycleC (k : ℕ → ℕ) : ℕ → ℕ
  | 0       => 0
  | (m + 1) => 3 * cycleC k m + 2 ^ (partialA k m)

/-- **Telescoping closed form.** For any sequence with per-step identities
`2^{k i}·a(i+1) = 3·a i + 1`, after `m` steps:
`2^{A_m} · a_m = 3^m · a_0 + C_m`. Pure induction. -/
theorem cycle_telescope (a k : ℕ → ℕ)
    (hstep : ∀ i, 2 ^ (k i) * a (i + 1) = 3 * a i + 1) :
    ∀ m, 2 ^ (partialA k m) * a m = 3 ^ m * a 0 + cycleC k m := by
  intro m
  induction m with
  | zero => simp [partialA, cycleC]
  | succ m ih =>
    have hAeq : partialA k (m + 1) = partialA k m + k m := rfl
    have hCeq : cycleC k (m + 1) = 3 * cycleC k m + 2 ^ (partialA k m) := rfl
    calc 2 ^ (partialA k (m + 1)) * a (m + 1)
        = 2 ^ (partialA k m) * (2 ^ (k m) * a (m + 1)) := by
          rw [hAeq, pow_add]; ring
      _ = 2 ^ (partialA k m) * (3 * a m + 1) := by rw [hstep m]
      _ = 3 * (2 ^ (partialA k m) * a m) + 2 ^ (partialA k m) := by ring
      _ = 3 * (3 ^ m * a 0 + cycleC k m) + 2 ^ (partialA k m) := by rw [ih]
      _ = 3 ^ (m + 1) * a 0 + cycleC k (m + 1) := by rw [hCeq, pow_succ]; ring

/-- **The cycle equation (additive form, no subtraction).** A periodic point
`a_m = a_0` of the step relation satisfies `2^{A_m}·a_0 = 3^m·a_0 + C_m`. -/
theorem cycle_equation (a k : ℕ → ℕ)
    (hstep : ∀ i, 2 ^ (k i) * a (i + 1) = 3 * a i + 1) (m : ℕ)
    (hcyc : a m = a 0) :
    2 ^ (partialA k m) * a 0 = 3 ^ m * a 0 + cycleC k m := by
  have h := cycle_telescope a k hstep m
  rwa [hcyc] at h

/-- The cycle constant is positive for `m ≥ 1`. -/
theorem cycleC_pos (k : ℕ → ℕ) {m : ℕ} (hm : 0 < m) : 0 < cycleC k m := by
  cases m with
  | zero => exact absurd hm (lt_irrefl 0)
  | succ m =>
    have hp : 0 < 2 ^ (partialA k m) := pow_pos (by norm_num) _
    have he : cycleC k (m + 1) = 3 * cycleC k m + 2 ^ (partialA k m) := rfl
    omega

/-- **Cycle corridor (strict).** A nontrivial (`m ≥ 1`) cycle with positive
element forces `3^m < 2^{A_m}` — the slope must sit strictly above the
critical line `log₂3`. -/
theorem forward_cycle_corridor (a k : ℕ → ℕ)
    (hstep : ∀ i, 2 ^ (k i) * a (i + 1) = 3 * a i + 1) (m : ℕ)
    (hcyc : a m = a 0) (hm : 0 < m) :
    3 ^ m < 2 ^ (partialA k m) := by
  have heq := cycle_equation a k hstep m hcyc
  have hC := cycleC_pos k hm
  by_contra hle
  have hle' : 2 ^ (partialA k m) ≤ 3 ^ m := not_lt.mp hle
  have hmul := Nat.mul_le_mul hle' (le_refl (a 0))
  omega

/-- **Grounding in real Collatz.** Any genuine periodic point `a0` of the
Syracuse map (`Syr^[m] a0 = a0`) satisfies the cycle equation with the actual
2-adic valuations `k_i = ν₂(3·Syr^[i](a0)+1)`. -/
theorem syr_cycle_equation (a0 m : ℕ) (h : (Syr^[m]) a0 = a0) :
    2 ^ (partialA (fun i => padicValNat 2 (3 * (Syr^[i]) a0 + 1)) m) * a0
      = 3 ^ m * a0
        + cycleC (fun i => padicValNat 2 (3 * (Syr^[i]) a0 + 1)) m := by
  have hstep : ∀ i,
      2 ^ (padicValNat 2 (3 * (Syr^[i]) a0 + 1)) * (Syr^[i + 1]) a0
        = 3 * (Syr^[i]) a0 + 1 := by
    intro i
    rw [Function.iterate_succ_apply']
    exact Syr_step ((Syr^[i]) a0)
  have key := cycle_telescope (fun i => (Syr^[i]) a0)
      (fun i => padicValNat 2 (3 * (Syr^[i]) a0 + 1)) hstep m
  simp only [Function.iterate_zero_apply] at key
  rw [h] at key
  exact key

/-- **Strict corridor for genuine Syracuse cycles.** A periodic point of `Syr`
of period `m ≥ 1` forces `3^m < 2^{A_m}` — the slope sits strictly above the
critical line `log₂3`. (Positivity of the cycle element is automatic: `Syr` has
no `0`-periodic point.) Derived from `syr_cycle_equation`. -/
theorem syr_cycle_corridor (a0 m : ℕ) (hm : 0 < m)
    (h : (Syr^[m]) a0 = a0) :
    3 ^ m < 2 ^ (partialA (fun i => padicValNat 2 (3 * (Syr^[i]) a0 + 1)) m) := by
  have heq := syr_cycle_equation a0 m h
  have hC := cycleC_pos (fun i => padicValNat 2 (3 * (Syr^[i]) a0 + 1)) hm
  by_contra hle
  have hle' :
      2 ^ (partialA (fun i => padicValNat 2 (3 * (Syr^[i]) a0 + 1)) m) ≤ 3 ^ m :=
    not_lt.mp hle
  have hmul := Nat.mul_le_mul hle' (le_refl a0)
  omega

/-- Sanity: the trivial cycle `{1}` (`a ≡ 1`, `k ≡ 2`, `m = 1`) satisfies the
cycle equation: `2^2·1 = 3·1 + 1`. -/
theorem trivial_cycle_satisfies_equation :
    2 ^ (partialA (fun _ => 2) 1) * (1 : ℕ)
      = 3 ^ 1 * 1 + cycleC (fun _ => 2) 1 := by
  decide

/-- **No nontrivial fixed point (period m = 1, UNCONDITIONAL, Baker-free).**
The only positive fixed point of `Syr` is `a = 1`. Proof: `Syr a = a` gives
`a · 2^{ν₂(3a+1)} = 3a + 1`, hence `a ∣ 3a+1`; since `a ∣ 3a`, `a ∣ 1`, so a = 1.
This settles the period-1 case of the cycle conjecture without transcendence —
the first genuine, unconditional cycle-exclusion result of the line. -/
theorem syr_no_nontrivial_fixedpoint (a : ℕ) (_ha : 0 < a) (h : Syr a = a) :
    a = 1 := by
  have hstep : 2 ^ (padicValNat 2 (3 * a + 1)) * a = 3 * a + 1 := by
    have hs := Syr_step a; rwa [h] at hs
  have hdvd : a ∣ 3 * a + 1 :=
    ⟨2 ^ (padicValNat 2 (3 * a + 1)), hstep.symm.trans (Nat.mul_comm _ _)⟩
  have hdvd3 : a ∣ 3 * a := dvd_mul_left a 3
  have h1 : a ∣ 1 := (Nat.dvd_add_right hdvd3).mp hdvd
  exact Nat.dvd_one.mp h1

/-- **No nontrivial 2-cycle (period m = 2, UNCONDITIONAL, Baker-free).** Any point
of period dividing 2 under `Syr` is the fixed point `1`. Proof: multiplying the
two step identities `2^{k₀}·b = 3a+1`, `2^{k₁}·a = 3b+1` (with `b = Syr a`) gives
`ab·(2^{k₀+k₁} − 9) = 3(a+b)+1`. Positivity forces `2^{k₀+k₁} > 9`, hence `≥ 16`,
so `7ab ≤ 3a+3b+1`, which for `a, b ≥ 1` forces `a = b = 1`. Settles period 2
without transcendence. -/
theorem syr_no_nontrivial_2cycle (a : ℕ) (ha : 0 < a) (h : (Syr^[2]) a = a) :
    a = 1 := by
  set b := Syr a with hbdef
  have hi : 2 ^ (padicValNat 2 (3 * a + 1)) * b = 3 * a + 1 := Syr_step a
  have ha_eq : Syr b = a := by
    have h2 := h
    rwa [Function.iterate_succ_apply', Function.iterate_one] at h2
  have hii : 2 ^ (padicValNat 2 (3 * b + 1)) * a = 3 * b + 1 := by
    have hs := Syr_step b; rw [ha_eq] at hs; exact hs
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hi; omega
    · exact h0
  have hmul :
      (2 ^ (padicValNat 2 (3 * a + 1)) * b) * (2 ^ (padicValNat 2 (3 * b + 1)) * a)
        = (3 * a + 1) * (3 * b + 1) := by rw [hi, hii]
  have e :
      (2 ^ (padicValNat 2 (3 * a + 1)) * b) * (2 ^ (padicValNat 2 (3 * b + 1)) * a)
        = 2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) * (a * b) := by
    rw [pow_add]; ring
  have hstar :
      2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) * (a * b)
        = 9 * (a * b) + 3 * a + 3 * b + 1 := by
    rw [← e, hmul]; ring
  have hAgt : 9 < 2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) := by
    have h1 : 9 * (a * b)
        < 2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) * (a * b) := by
      omega
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
  have hA4 : 4 ≤ padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1) := by
    by_contra hc
    rw [not_le] at hc
    have hle : 2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h83 : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  have h16 : 16 ≤ 2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) := by
    have h4 : (2 : ℕ) ^ 4
        ≤ 2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) :=
      Nat.pow_le_pow_right (by norm_num) hA4
    have h44 : (2 : ℕ) ^ 4 = 16 := by norm_num
    omega
  have hbig : 16 * (a * b)
      ≤ 2 ^ (padicValNat 2 (3 * a + 1) + padicValNat 2 (3 * b + 1)) * (a * b) :=
    Nat.mul_le_mul h16 (le_refl (a * b))
  have h7 : 7 * (a * b) ≤ 3 * a + 3 * b + 1 := by omega
  have hab_a : a ≤ a * b := le_mul_of_one_le_right (Nat.zero_le a) hb1
  have hab_b : b ≤ a * b := le_mul_of_one_le_left (Nat.zero_le b) ha
  omega

/-- **The cycle conjecture** (the "no nontrivial cycles" half of Collatz): the
only positive periodic point of `Syr` is `a = 1`. The period-1 and period-2 cases
are PROVEN unconditionally (`syr_no_nontrivial_fixedpoint`,
`syr_no_nontrivial_2cycle`). The general statement is UNPROVEN — the unconditional
proof for unbounded period needs an effective lower bound on `|2^A − 3^m|` (linear
forms in logarithms, Baker/Matveev), absent from Mathlib. Stated, never assumed. -/
def NoNontrivialSyrCycle : Prop :=
  ∀ (a0 m : ℕ), 0 < a0 → 0 < m → (Syr^[m]) a0 = a0 → a0 = 1

end CollatzLean4.Admissible
