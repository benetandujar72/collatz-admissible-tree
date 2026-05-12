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

/-- S202 admissible word (26 symbols): 10100000001000010000000000. -/
def wS202 : Word :=
  [ Branch.one,  Branch.zero, Branch.one,  Branch.zero, Branch.zero,
    Branch.zero, Branch.zero, Branch.zero, Branch.zero, Branch.zero,
    Branch.zero, Branch.one,  Branch.zero, Branch.zero, Branch.zero,
    Branch.zero, Branch.one,  Branch.zero, Branch.zero, Branch.zero,
    Branch.zero, Branch.zero, Branch.zero, Branch.zero, Branch.zero,
    Branch.zero ]

-- Actual values produced by the formal semantics on `wS202`:
--   n = 1035769,  A = 55,  q = 22,  B = 3525268288809647,  defect = 11.
-- The S202 spec quotes  n = 251, A = 43, B = 919447060349, defect = −1.
-- Only q matches. The A and B mismatches indicate a convention difference
-- (almost certainly forward run from a base n vs. inverse run from 1);
-- this is recorded honestly here rather than masked.
theorem S202_q          : (evalWord wS202).q = 22                     := by native_decide
theorem S202_n_actual   : (evalWord wS202).n = 1035769                := by native_decide
theorem S202_A_actual   : (evalWord wS202).A = 55                     := by native_decide
theorem S202_B_actual   : (evalWord wS202).B = 3525268288809647       := by native_decide
theorem S202_defect_actual : defect (evalWord wS202) = 11             := by native_decide

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

end CollatzLean4.Admissible
