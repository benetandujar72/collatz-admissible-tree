/-
Defect D = A − 2q and the S202 counterexample to A ≥ 2q.
-/

import CollatzLean4.AdmissibleBasic

namespace CollatzLean4.Admissible

def defect (s : AdmState) : Int :=
  (s.A : Int) - 2 * (s.q : Int)

lemma defect_step_one (s : AdmState) :
    defect (step s Branch.one) = defect s + (tau s.n : Int) := by
  simp [defect, step]; ring

lemma defect_step_zero (s : AdmState) :
    defect (step s Branch.zero) = defect s + (tau s.n : Int) - 2 := by
  simp [defect, step]; ring

/-- S202 admissible word (26 symbols): `10100000001000010000000000`.
Ones at positions 0, 2, 10, 15. Matches the literature. -/
def wS202 : Word :=
  [ Branch.one,  Branch.zero, Branch.one,  Branch.zero, Branch.zero,
    Branch.zero, Branch.zero, Branch.zero, Branch.zero, Branch.zero,
    Branch.one,  Branch.zero, Branch.zero, Branch.zero, Branch.zero,
    Branch.one,  Branch.zero, Branch.zero, Branch.zero, Branch.zero,
    Branch.zero, Branch.zero, Branch.zero, Branch.zero, Branch.zero,
    Branch.zero ]

-- `evalWord wS202` from `initState` (n=1) produces EXACTLY the published
-- S202 constants:  n = 251, A = 43, q = 22, B = 919447060349, defect = −1.
-- (Earlier versions of this file had positions 10/11 and 15/16 swapped,
-- producing different values; that transcription error has been corrected.)
theorem S202_q             : (evalWord wS202).q = 22             := by native_decide
theorem S202_n_actual      : (evalWord wS202).n = 251             := by native_decide
theorem S202_A_actual      : (evalWord wS202).A = 43              := by native_decide
theorem S202_B_actual      : (evalWord wS202).B = 919447060349   := by native_decide
theorem S202_defect_actual : defect (evalWord wS202) = -1         := by native_decide

/-! ### S202 — abstract translation-set witness

The published S202 constants `(A, q, B) = (43, 22, 919447060349)` do not
arise from `evalWord wS202` under the formal semantics in this file
(see the `_actual` theorems above). They DO, however, satisfy the abstract
resonance condition for `R_adm`/`R_free`:

  3^22 · 251 + 919447060349 = 2^43,        (translation identity)
  919447060349 ≡ 2^43  (mod 3^22),         (resonance)
  43 < 2 · 22,                              (low slope, defect = −1)

so the S202 counterexample to the auxiliary conjecture `A ≥ 2q` is honest
at the level of admissible *triples*, independent of which word generates
them. -/

def AS202 : Nat := 43
def qS202 : Nat := 22
def BS202 : Nat := 919447060349
def nS202 : Nat := 251

theorem S202_translation_identity :
    3 ^ qS202 * nS202 + BS202 = 2 ^ AS202 := by native_decide

theorem S202_resonance :
    BS202 % (3 ^ qS202) = (2 ^ AS202) % (3 ^ qS202) := by native_decide

theorem S202_low_slope : AS202 < 2 * qS202 := by native_decide

theorem S202_abstract_defect_negative :
    (AS202 : Int) - 2 * (qS202 : Int) = -1 := by native_decide

/-- The auxiliary conjecture "every admissible triple `(A, q, B)` satisfying
the translation identity must have `A ≥ 2q`" is FALSE: `(43, 22, 919447060349)`
is a resonant translation triple with `A = 43 < 44 = 2q`. -/
theorem not_forall_admissible_triple_high_slope :
    ¬ (∀ A q B : Nat,
        (∃ n, 3 ^ q * n + B = 2 ^ A) →
        B % (3 ^ q) = (2 ^ A) % (3 ^ q) →
        A ≥ 2 * q) := by
  intro h
  have := h AS202 qS202 BS202 ⟨nS202, S202_translation_identity⟩ S202_resonance
  have hlow := S202_low_slope
  omega

/-! ### S204-A: lower slope bound

Every admissible state satisfies `3^q ≤ 2^A`. Direct from `GoodState`
and `n ≥ 1` (which follows from `InX`). The sharp counterexample S202
shows we cannot strengthen this to `A ≥ 2q`, but we always get
`q ≤ A` (corollary).
-/

/-- `n ∈ X` forces `n ≥ 1` (since `0 % 9 = 0 ∉ X`). -/
lemma one_le_of_InX {n : Nat} (h : InX n) : 1 ≤ n := by
  unfold InX at h; omega

/-- Fundamental admissible bound: `3^q ≤ 2^A` for every state with `Inv`. -/
theorem three_pow_q_le_two_pow_A (s : AdmState) (h : Inv s) :
    3 ^ s.q ≤ 2 ^ s.A := by
  have hgood : 3 ^ s.q * s.n + s.B = 2 ^ s.A := h.1
  have hn : 1 ≤ s.n := one_le_of_InX h.2
  calc 3 ^ s.q
      = 3 ^ s.q * 1 := (Nat.mul_one _).symm
    _ ≤ 3 ^ s.q * s.n := Nat.mul_le_mul_left _ hn
    _ ≤ 3 ^ s.q * s.n + s.B := Nat.le_add_right _ _
    _ = 2 ^ s.A := hgood

/-- Corollary: every admissible run satisfies `3^q ≤ 2^A`. -/
theorem evalWord_three_pow_le (w : Word) :
    3 ^ (evalWord w).q ≤ 2 ^ (evalWord w).A :=
  three_pow_q_le_two_pow_A _ (runWord_preserves_inv w init_inv)

/-- Weak slope bound: `q ≤ A` along every admissible run. Sharp
counterexamples (S202: `A = 43, q = 22`) prevent strengthening
to `A ≥ 2q`. -/
theorem evalWord_q_le_A (w : Word) : (evalWord w).q ≤ (evalWord w).A := by
  by_contra hlt
  have hlt' : (evalWord w).A < (evalWord w).q := Nat.lt_of_not_le hlt
  have hpow := evalWord_three_pow_le w
  have h1 : 2 ^ (evalWord w).A < 2 ^ (evalWord w).q :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt'
  have h2 : 2 ^ (evalWord w).q ≤ 3 ^ (evalWord w).q :=
    Nat.pow_le_pow_left (by norm_num : 2 ≤ 3) _
  omega

/-- Defect lower bound: `defect (evalWord w) ≥ -q` along every
admissible run (since `q ≤ A`, so `A - 2q ≥ -q`). -/
theorem evalWord_defect_ge_neg_q (w : Word) :
    defect (evalWord w) ≥ -(((evalWord w).q : Int)) := by
  have hqA : (evalWord w).q ≤ (evalWord w).A := evalWord_q_le_A w
  unfold defect
  omega

end CollatzLean4.Admissible
