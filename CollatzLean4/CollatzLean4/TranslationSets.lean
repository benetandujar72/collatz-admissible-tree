/-
Admissible and free translation sets B_adm, B_free, R_adm, R_free,
and the equivalence between word-coverage and translation-coverage.
-/

import CollatzLean4.AdmissibleBasic

namespace CollatzLean4.Admissible

def B_adm (A q B : Nat) : Prop :=
  ∃ w : Word,
    (evalWord w).A = A ∧ (evalWord w).q = q ∧ (evalWord w).B = B

def P_adm (A q : Nat) : Prop := ∃ B, B_adm A q B

def R_adm (A q B : Nat) : Prop :=
  B_adm A q B ∧ B % (3 ^ q) = (2 ^ A) % (3 ^ q)

/-- Free B's, built from strictly-decreasing exponent lists  c_m < A.  -/
def B_of_cs : List Nat → Nat
  | []        => 0
  | c :: cs   => 2 ^ c + 3 * B_of_cs cs

def StrictDecBelow (A : Nat) (cs : List Nat) : Prop :=
  (∀ c ∈ cs, c < A) ∧ cs.Pairwise (· > ·)

def B_free (A q B : Nat) : Prop :=
  ∃ cs : List Nat,
    cs.length = q ∧ StrictDecBelow A cs ∧ B_of_cs cs = B

def R_free (A q B : Nat) : Prop :=
  B_free A q B ∧ B % (3 ^ q) = (2 ^ A) % (3 ^ q)

def InImageTheta (n : Nat) : Prop := ∃ w : Word, (evalWord w).n = n

/-- S191-E: equivalence between word-coverage and translation-coverage.
    Proof reserved. -/
theorem coverage_translation_equiv :
    (∀ n : Nat, InX n → InImageTheta n)
    ↔
    (∀ n : Nat, InX n →
      ∃ A q B : Nat, B_adm A q B ∧ 3 ^ q * n + B = 2 ^ A) := by
  sorry

end CollatzLean4.Admissible
