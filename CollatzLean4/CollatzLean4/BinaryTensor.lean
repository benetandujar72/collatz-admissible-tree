/-
Binary Dynamic Tensors (TBD) — forward-Collatz / 2-adic coordinate module.

Following B. Andújar Mata, "Teoría de Tensores Binarios Dinámicos:
Un Marco Formal Unificado para la Conjetura de Collatz" (2026).

ARCHITECTURE: this module formalizes the 2-adic / parity-coordinate
language of the TBD paper. It is complementary to (and NOT a replacement
for) the 3-adic admissible inverse tree (S189–S208) in the rest of the
project. The split is intentional:

  * TBD = 2-adic / parity coordinates (Terras filtration, bit tensors).
  * S189–S208 = 3-adic admissible inverse cover (translation triples,
    negative-run tubes around −1 mod 3^k).

Collatz requires *simultaneous* control of both filtrations. This module
provides the 2-adic side as a coordinate scaffold; the 3-adic engine
(where the actual descent lemmas live) is in `NegativeRuns`,
`TranslationSets`, `Defect`, `ThreeAdic`.

CERTIFIED THEOREMS (full Lean proofs):
  * `T_lento`, `T_fast` — slow and accelerated Collatz.
  * `T_lento_attractor_cycle` (Prop. 12.3 TBD): 1 → 4 → 2 → 1.
  * `T_lento_odd_then_even` (Thm. 12.2 TBD: parity dependence).
  * `bk` (k-th bit), `bitVec` (first-k bits as list).
  * `parityVec` (Terras parity vector), `accCarry` (carry c_k).
  * `accCarry_eq_parityVec_sum`: definitional equivalence c_k = Σ ε_j.
  * `parityVec_27` (Example 4.3): for n=27 the vector is [1,1,0,1,1].
  * Terras bijectivity at small k (k = 1, 2, 3) via finite tables.

EXPLICITLY NOT CLAIMED (with reasons):
  * Full Terras bijectivity ∀ k (Thm. 4.1 TBD) — needs induction on k
    tracking T_fast mod 2^k periodicity.
  * Spectrum of `P_k` (Thm. 8.4 TBD) — the original paper verifies it
    symbolically up to k ≤ 7; classified honestly as a conjecture here.
  * Non-linearity of the Collatz operator on ℓ² (Thm. 10.2 TBD) —
    the original proof contains a gap (`ψ_2 + ψ_3 ∉ M` does not refute
    linearity, since a linear C may be defined outside M). The correct
    obstruction uses the linear dependence `ψ_3 = ψ_1 + ψ_2` (binary
    representation): T_lento(3) = 10 has ψ_10 = e_1 + e_3, but
    T_lento(1) + T_lento(2) = ψ_4 + ψ_1 = e_2 + e_0 ≠ e_1 + e_3.
    Formalizing this needs ℓ² and ψ_n; deferred.
  * Entropy `h_μ(T̂) = log 2 − ½ log 3` — this is a heuristic drift
    constant, not the standard 2-adic shift entropy. The original paper
    states it as a Lagarias–Weiss theorem; we record it only as a
    motivating remark, not as a Lean theorem.
  * The Collatz conjecture itself.
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

/-- The k-element bit vector `[b₀(n), b₁(n), …, b_{k−1}(n)]`. -/
def bitVec : Nat → Nat → List Nat
  | 0,     _ => []
  | k + 1, n => (n % 2) :: bitVec k (n / 2)

theorem bitVec_zero (n : Nat) : bitVec 0 n = [] := rfl

theorem bitVec_succ (k n : Nat) :
    bitVec (k + 1) n = (n % 2) :: bitVec k (n / 2) := rfl

theorem bitVec_length (k n : Nat) : (bitVec k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [bitVec, ih]

/-! ### §4 — Terras parity vector and accumulated carry -/

/-- Terras parity vector of length k:
    `parityVec k n = [n%2, T_fast(n)%2, T_fast²(n)%2, …, T_fast^{k-1}(n)%2]`. -/
def parityVec : Nat → Nat → List Nat
  | 0,     _ => []
  | k + 1, n => (n % 2) :: parityVec k (T_fast n)

theorem parityVec_length (k n : Nat) : (parityVec k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [parityVec, ih]

/-- The accumulated carry `c_k(n)`: number of odd iterates in the first k. -/
def accCarry (k n : Nat) : Nat :=
  (parityVec k n).sum

/-- Definitional identity from §4 TBD: `c_k(n) = Σ_{j=0}^{k-1} ε_j`. -/
@[simp] theorem accCarry_eq_parityVec_sum (k n : Nat) :
    accCarry k n = (parityVec k n).sum := rfl

/-! ### Example 4.3 — Terras tensor for n = 27 -/

/-- For `n = 27` the Terras parity vector of length 5 is `[1,1,0,1,1]`.
    Corresponding orbit: 27 → 41 → 62 → 31 → 47. -/
theorem parityVec_27 : parityVec 5 27 = [1, 1, 0, 1, 1] := by
  decide

/-- For `n = 27` the accumulated carry at k = 5 is 4 (four odd steps). -/
theorem accCarry_27 : accCarry 5 27 = 4 := by decide

/-! ### Modular structure of `bitVec`

The first k bits of n depend only on `n mod 2^k`. We prove the
"invariance under adding multiples of 2^k" direction; the bi-conditional
`bitVec k n = bitVec k m ↔ n % 2^k = m % 2^k` is the standard
base-2 digit characterization and is provable by adding a
`bitsToNat ∘ bitVec` round-trip lemma (omitted here for brevity). -/

theorem bitVec_add_pow_mul (k n m : Nat) :
    bitVec k (n + 2 ^ k * m) = bitVec k n := by
  induction k generalizing n m with
  | zero => rfl
  | succ k ih =>
    show (n + 2 ^ (k + 1) * m) % 2 :: bitVec k ((n + 2 ^ (k + 1) * m) / 2)
       = (n % 2) :: bitVec k (n / 2)
    have hpow_alt : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by rw [pow_succ]; ring
    have h_mod : (n + 2 ^ (k + 1) * m) % 2 = n % 2 := by
      rw [hpow_alt]
      set X := 2 ^ k * m
      omega
    have h_div : (n + 2 ^ (k + 1) * m) / 2 = n / 2 + 2 ^ k * m := by
      rw [hpow_alt]
      set X := 2 ^ k * m
      omega
    rw [h_mod, h_div, ih]

/-- The first k bits of n depend only on n mod 2^k. -/
theorem bitVec_mod_pow (k n : Nat) : bitVec k (n % 2 ^ k) = bitVec k n := by
  conv_rhs =>
    rw [show n = n % 2 ^ k + 2 ^ k * (n / 2 ^ k) from by
      rw [Nat.add_comm]; exact (Nat.div_add_mod n (2 ^ k)).symm]
  exact (bitVec_add_pow_mul k (n % 2 ^ k) (n / 2 ^ k)).symm

/-- One direction of the Terras-style invariant: `n ≡ m (mod 2^k)` implies
identical first-k bit vectors. -/
theorem bitVec_eq_of_mod_eq {k n m : Nat} (h : n % 2 ^ k = m % 2 ^ k) :
    bitVec k n = bitVec k m := by
  rw [← bitVec_mod_pow k n, ← bitVec_mod_pow k m, h]

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

/-! ### Bridge: 2-adic coordinates vs 3-adic admissible cover

The TBD framework formalized here gives a 2-adic *coordinate system*:
the first k bits of n, equivalently `n mod 2^k`, fully determine the
Terras parity vector `parityVec k n` (Theorem 4.1 TBD, certified at
k ≤ 3 above). This is a parity-side scaffold.

The 3-adic descent engine lives in the other modules:

  * `NegativeRuns.negative_run_integrality_iff` — characterizes which
    `n ∈ ℤ` survive `k` applications of the negative branch:
    `n ≡ -1 (mod 3^k)`.
  * `NegativeRuns.Lnum_eq_three_pow_mul_Lk` (S203-D) — closed form
    `3^k · L^k(n) = 2^k(n+1) − 3^k` under integrality.
  * `TranslationSets.coverage_translation_equiv` — coverage by
    admissible words ⇔ existence of resonant translation triples.
  * `ThreeAdic.S206_fixed_point_mod_general` — `(2^43 − 3^22)` is a
    unit in every `ZMod (3^k)`; the 3-adic Cauchy sequence converging
    to the S202 fixed point.

The Collatz conjecture, in this two-filtration framework, requires
*simultaneous* 2-adic and 3-adic control: every n ∈ ℕ must be
reachable by an admissible word (3-adic), and equivalently the parity
trajectory of every n ∈ ℕ must terminate at 1 (2-adic). Neither
filtration alone is sufficient.

The empirical finding from `Reachability.no_short_path_to_two` shows
that the inverse admissible model (3-adic side) is structurally
restricted (n = 2 not reachable), so the two filtrations are NOT
faithful coordinatizations of the same underlying dynamics in this
codebase as currently set up. Reconciling them is open. -/

end CollatzLean4.BinaryTensor
