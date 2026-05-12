/-
Copyright (c) 2026 Benet Andújar Guardado.

Admissible inverse Mori–Andújar tree — basic definitions.

Formalizes:
  * inverse branches Ψ₀, Ψ₁,
  * accumulated parameters (n, A, q, B),
  * the translation identity  3^q · n + B = 2^A.

Does NOT prove Collatz. Open problems are flagged explicitly.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace CollatzLean4.Admissible

inductive Branch where
  | zero : Branch
  | one  : Branch
deriving DecidableEq, Repr

abbrev Word := List Branch

/-- τ table on n mod 9 over the admissible section X₉ = {1,2,4,5,7,8}. -/
def tau (n : Nat) : Nat :=
  match n % 9 with
  | 1 => 2
  | 2 => 1
  | 4 => 2
  | 5 => 3
  | 7 => 4
  | 8 => 1
  | _ => 0

def InX (n : Nat) : Prop :=
  n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 4 ∨
  n % 9 = 5 ∨ n % 9 = 7 ∨ n % 9 = 8

structure AdmState where
  n : Nat
  A : Nat
  q : Nat
  B : Nat
deriving Repr, DecidableEq

def initState : AdmState := { n := 1, A := 0, q := 0, B := 0 }

def step (s : AdmState) (b : Branch) : AdmState :=
  let t := tau s.n
  match b with
  | Branch.one =>
      { n := 2 ^ t * s.n,
        A := s.A + t,
        q := s.q,
        B := 2 ^ t * s.B }
  | Branch.zero =>
      { n := (2 ^ t * s.n - 1) / 3,
        A := s.A + t,
        q := s.q + 1,
        B := 2 ^ t * s.B + 3 ^ s.q }

def runWord : Word → AdmState → AdmState
  | [], s => s
  | b :: bs, s => runWord bs (step s b)

def evalWord (w : Word) : AdmState := runWord w initState

def stateFrom (n : Nat) : AdmState := { n := n, A := 0, q := 0, B := 0 }
def evalWordFrom (n : Nat) (w : Word) : AdmState := runWord w (stateFrom n)

/-- Translation invariant. -/
def GoodState (s : AdmState) : Prop :=
  3 ^ s.q * s.n + s.B = 2 ^ s.A

lemma init_good : GoodState initState := by
  simp [GoodState, initState]

/-- "one" branch preserves the translation identity (pure algebra). -/
lemma step_one_good {s : AdmState} (h : GoodState s) :
    GoodState (step s Branch.one) := by
  unfold GoodState step
  simp only
  have key : 3 ^ s.q * (2 ^ tau s.n * s.n) + 2 ^ tau s.n * s.B
           = 2 ^ tau s.n * (3 ^ s.q * s.n + s.B) := by ring
  rw [key, h, pow_add, Nat.mul_comm]

/-- "zero" branch preserves the identity ONLY when 3 ∣ 2^τ(n)·n − 1,
    i.e. for n ∈ X (case analysis on n % 9). Left open pending that
    integrality lemma — the lemma as stated for arbitrary `s` is false
    in `Nat` because of truncated subtraction. -/
lemma step_zero_good {s : AdmState}
    (hX : InX s.n) (h : GoodState s) :
    GoodState (step s Branch.zero) := by
  sorry

/-- Joint invariant carried along admissible runs. -/
def Inv (s : AdmState) : Prop := GoodState s ∧ InX s.n

lemma init_inv : Inv initState := by
  refine ⟨init_good, ?_⟩
  -- 1 % 9 = 1
  left; decide

/-- τ depends only on n mod 9. -/
lemma tau_mod (n : Nat) : tau n = tau (n % 9) := by
  unfold tau; rw [Nat.mod_mod]

/-- The "one" branch preserves InX: case analysis on n % 9. -/
lemma step_one_preserves_X {s : AdmState} (hX : InX s.n) :
    InX (step s Branch.one).n := by
  show InX (2 ^ tau s.n * s.n)
  unfold InX at hX ⊢
  have hmul : (2 ^ tau s.n * s.n) % 9
            = ((2 ^ tau s.n) % 9 * (s.n % 9)) % 9 := Nat.mul_mod _ _ _
  rw [hmul]
  rcases hX with h | h | h | h | h | h <;>
    (rw [h, tau_mod, h]; unfold tau; decide)

/-- The "zero" branch preserves InX. Case analysis on n % 9 left as sorry. -/
lemma step_zero_preserves_X {s : AdmState} (hX : InX s.n) :
    InX (step s Branch.zero).n := by
  sorry

lemma step_inv {s : AdmState} (h : Inv s) :
    ∀ b, Inv (step s b)
  | Branch.one  => ⟨step_one_good h.1, step_one_preserves_X h.2⟩
  | Branch.zero => ⟨step_zero_good h.2 h.1, step_zero_preserves_X h.2⟩

theorem runWord_preserves_inv (w : Word) {s : AdmState}
    (h : Inv s) : Inv (runWord w s) := by
  induction w generalizing s with
  | nil => simpa [runWord] using h
  | cons b bs ih => exact ih (step_inv h b)

/-- Central identity (S189–S191):  3^q · n + B = 2^A. -/
theorem evalWord_translation_identity (w : Word) :
    GoodState (evalWord w) :=
  (runWord_preserves_inv w init_inv).1

end CollatzLean4.Admissible
