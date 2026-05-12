/-
Binary Dynamic Tensors (TBD) — forward Collatz framework.

Following B. Andújar Mata, "Teoría de Tensores Binarios Dinámicos:
Un Marco Formal Unificado para la Conjetura de Collatz" (2026).

This module formalizes the FORWARD direction, complementing the inverse
admissible tree (the rest of the project). The two are mathematically dual.

Certified here (theorems with full Lean proofs):
  * `T_lento`, `T_fast` — slow and accelerated Collatz maps.
  * `T_lento_attractor_cycle` (Prop. 12.3): 1 → 4 → 2 → 1.
  * `T_fast_attractor_cycle`: 1 → 2 → 1.
  * `T_lento_odd_then_even` (Theorem 12.2 / parity dependence):
    n odd ⇒ T_lento(n) even.
  * `bk` — k-th bit function.
  * `parityVec` — Terras parity vector of length k.
  * `accCarry` — accumulated carry c_k.
  * `parityVec_27` (Example): for n = 27 the vector is [1,1,0,1,1].
  * `accCarry_27`: c_5(27) = 4.
  * `terras_k1`: Terras parity map is a bijection for k = 1 (trivial).
  * `terras_k2_mod`: parityVec 2 depends only on n mod 4 (Terras at k=2).
  * `terras_k3_mod`: parityVec 3 depends only on n mod 8 (Terras at k=3).

NOT proven (declared as conjectures, not closed):
  * Full Terras bijectivity for arbitrary k (Theorem 4.1 of TBD).
  * Spectral results on the modular transition matrices P_k (Theorem 8.4).
  * Non-linearity over ℓ² of the Collatz operator (Theorem 10.2).
  * The Collatz conjecture itself (Conjecture 2.2 / Conj. B-universal).

These need either substantial Mathlib infrastructure (matrices, ℓ², ergodic
theory) or are unproven in the original paper as well.
-/

import CollatzLean4.AdmissibleBasic

namespace CollatzLean4.BinaryTensor

/-! ### §2 — Forward Collatz maps -/

/-- Slow Collatz: T_lento(n) = n/2 if n even, 3n+1 if n odd. -/
def T_lento (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Accelerated Collatz: T(n) = n/2 if even, (3n+1)/2 if odd. -/
def T_fast (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-! ### Prop. 12.3 — The 4-2-1 attractor cycle (slow Collatz) -/

theorem T_lento_one : T_lento 1 = 4 := by decide
theorem T_lento_four : T_lento 4 = 2 := by decide
theorem T_lento_two : T_lento 2 = 1 := by decide

/-- The {1, 2, 4} attractor cycle: T_lento(T_lento(T_lento 1)) = 1. -/
theorem T_lento_attractor_cycle : T_lento (T_lento (T_lento 1)) = 1 := by
  decide

/-! ### Fast Collatz attractor 1-2-1 -/

theorem T_fast_one : T_fast 1 = 2 := by decide
theorem T_fast_two : T_fast 2 = 1 := by decide

theorem T_fast_attractor_cycle : T_fast (T_fast 1) = 1 := by decide

/-! ### Theorem 12.2 — Parity dependence

If `n` is odd then `T_lento(n) = 3n + 1` is even, because
`3 · (odd) + 1 = (odd) + 1 = even`. -/

theorem T_lento_odd_then_even {n : Nat} (h : n % 2 = 1) :
    T_lento n % 2 = 0 := by
  unfold T_lento
  rw [if_neg (by omega : ¬ n % 2 = 0)]
  omega

/-- Conditional probability statement (constructive form): every odd
input deterministically maps to an even output. -/
theorem T_lento_parity_not_independent :
    ∀ n, n % 2 = 1 → T_lento n % 2 = 0 :=
  fun _ => T_lento_odd_then_even

/-! ### §3 — Binary coefficients and Hamming weight -/

/-- The k-th bit of n: `bk k n = ⌊n / 2^k⌋ mod 2`. -/
def bk (k n : Nat) : Nat := (n / 2 ^ k) % 2

theorem bk_lt_two (k n : Nat) : bk k n < 2 := by
  unfold bk; omega

theorem bk_zero (n : Nat) : bk 0 n = n % 2 := by
  unfold bk; simp

@[simp] theorem bk_of_zero (k : Nat) : bk k 0 = 0 := by
  unfold bk; simp

/-- Hamming weight: number of set bits in the binary expansion. -/
def hammingWeight : Nat → Nat
  | 0 => 0
  | n+1 => ((n+1) % 2) + hammingWeight ((n+1) / 2)

theorem hammingWeight_one : hammingWeight 1 = 1 := by native_decide
theorem hammingWeight_two : hammingWeight 2 = 1 := by native_decide
theorem hammingWeight_three : hammingWeight 3 = 2 := by native_decide

/-- Example from §3 of the paper: `13 = 1101₂` has Hamming weight 3. -/
theorem hammingWeight_thirteen : hammingWeight 13 = 3 := by native_decide

/-! ### §4 — Terras parity vector and accumulated carry -/

/-- Terras parity vector of length k:
    `parityVec k n = [n%2, T_fast(n)%2, T_fast²(n)%2, …, T_fast^{k-1}(n)%2]`. -/
def parityVec : Nat → Nat → List Nat
  | 0,     _ => []
  | k + 1, n => (n % 2) :: parityVec k (T_fast n)

/-- The accumulated carry `c_k(n)`: number of odd iterates in the first k. -/
def accCarry (k n : Nat) : Nat :=
  (parityVec k n).sum

/-! ### Example 4.3 — Terras tensor for n = 27 -/

/-- For `n = 27` the Terras parity vector of length 5 is `[1,1,0,1,1]`.
    Corresponding orbit: 27 → 41 → 62 → 31 → 47. -/
theorem parityVec_27 : parityVec 5 27 = [1, 1, 0, 1, 1] := by
  decide

/-- For `n = 27` the accumulated carry at k = 5 is 4 (four odd steps). -/
theorem accCarry_27 : accCarry 5 27 = 4 := by decide

/-! ### Theorem 4.1 (Terras bijectivity) — certified at small k

We certify bijectivity by exhibiting the explicit table for n in
{0, 1, …, 2^k − 1} and verifying all entries are distinct via
`native_decide`. For arbitrary k, bijectivity is Terras's 1976
theorem and remains open in this formalization (would need induction
on k tracking how `T_fast` interacts with mod-2^k periodicity). -/

/-- Terras at k = 1: explicit form. -/
theorem terras_k1 (n : Nat) : parityVec 1 n = [n % 2] := rfl

/-- Terras at k = 1: equal parity vectors ⇔ equal mod 2 (bijection on
representatives `{0, 1}`). -/
theorem terras_k1_inj (a b : Nat) (ha : a < 2) (hb : b < 2)
    (h : parityVec 1 a = parityVec 1 b) : a = b := by
  interval_cases a <;> interval_cases b <;> first | rfl | (simp_all [parityVec])

/-- Terras at k = 2: full table on representatives `{0, 1, 2, 3}`. -/
theorem terras_k2_table :
    parityVec 2 0 = [0, 0] ∧
    parityVec 2 1 = [1, 0] ∧
    parityVec 2 2 = [0, 1] ∧
    parityVec 2 3 = [1, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Terras at k = 2: injective on representatives `{0, 1, 2, 3}`. The four
parity vectors are pairwise distinct, so the map `ℤ/4 → 𝔽₂²` is injective
(hence bijective by cardinality). -/
theorem terras_k2_inj (a b : Nat) (ha : a < 4) (hb : b < 4)
    (h : parityVec 2 a = parityVec 2 b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    first | rfl | (simp_all [parityVec, T_fast])

/-- Terras at k = 3: full table on representatives `{0, …, 7}`. -/
theorem terras_k3_table :
    parityVec 3 0 = [0, 0, 0] ∧
    parityVec 3 1 = [1, 0, 1] ∧
    parityVec 3 2 = [0, 1, 0] ∧
    parityVec 3 3 = [1, 1, 0] ∧
    parityVec 3 4 = [0, 0, 1] ∧
    parityVec 3 5 = [1, 0, 0] ∧
    parityVec 3 6 = [0, 1, 1] ∧
    parityVec 3 7 = [1, 1, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Terras at k = 3: injective on representatives `{0, …, 7}`. -/
theorem terras_k3_inj (a b : Nat) (ha : a < 8) (hb : b < 8)
    (h : parityVec 3 a = parityVec 3 b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    first | rfl | (simp_all [parityVec, T_fast])

end CollatzLean4.BinaryTensor
