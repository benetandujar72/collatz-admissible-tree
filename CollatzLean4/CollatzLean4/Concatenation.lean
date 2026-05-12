/-
Concatenation of admissible words and the S210/S211 constructive
criterion for subcritical slope.

CONTENT:
  * `Word.repeat'` — n-fold append of a word.
  * `runWord_append` — running a concatenation = running second after first.
  * `defectChange` — the per-state defect delta induced by a word.
  * `defectChange_append`, `defectChange_repeat'_bounded` —
    additivity of defect change.
  * `S211_subcritical_criterion` — if `u` reaches a cylinder with
    `D(u) < m`, and `w` has uniform defect change `−1` along the
    iterated trajectory from `evalWord u`, then `defect(u w^m) < 0`,
    i.e. `A(u w^m) < 2·q(u w^m)`.

The criterion is CONDITIONAL on the cylinder-stability hypothesis (the
"uniform −1" assumption). Establishing this hypothesis for a concrete
word `w = wS202` reduces to the S209 stability lemma (formalization
left open — it depends on the fine 3-adic structure of `aS202`).

This module provides the formal scaffolding that converts the
algebraic concatenation identity `D(u w^m) = D(u) − m` from S210/S211
into a Lean theorem usable by the S202 access program.
-/

import CollatzLean4.Defect

namespace CollatzLean4.Admissible

/-! ### Word concatenation primitives -/

/-- `n`-fold concatenation of a word (append on the right).

  `Word.repeat' w 0 = []`
  `Word.repeat' w (n+1) = Word.repeat' w n ++ w`. -/
def Word.repeat' (w : Word) : Nat → Word
  | 0     => []
  | n + 1 => Word.repeat' w n ++ w

@[simp] theorem Word.repeat'_zero (w : Word) : Word.repeat' w 0 = [] := rfl

theorem Word.repeat'_succ (w : Word) (n : Nat) :
    Word.repeat' w (n + 1) = Word.repeat' w n ++ w := rfl

/-- Running a concatenated word: first run `w1`, then `w2` from there. -/
theorem runWord_append (w1 w2 : Word) (s : AdmState) :
    runWord (w1 ++ w2) s = runWord w2 (runWord w1 s) := by
  induction w1 generalizing s with
  | nil => rfl
  | cons b bs ih =>
      show runWord (bs ++ w2) (step s b)
         = runWord w2 (runWord bs (step s b))
      exact ih (step s b)

/-! ### Defect change -/

/-- The defect delta of running `w` from state `s`. -/
def defectChange (w : Word) (s : AdmState) : Int :=
  defect (runWord w s) - defect s

theorem defectChange_def (w : Word) (s : AdmState) :
    defectChange w s = defect (runWord w s) - defect s := rfl

/-- Defect change is additive under concatenation. -/
theorem defectChange_append (w1 w2 : Word) (s : AdmState) :
    defectChange (w1 ++ w2) s
      = defectChange w1 s + defectChange w2 (runWord w1 s) := by
  unfold defectChange
  rw [runWord_append]
  ring

/-- The full defect after running a concatenation, in terms of pieces. -/
theorem defect_runWord_append (w1 w2 : Word) (s : AdmState) :
    defect (runWord (w1 ++ w2) s)
      = defect s + defectChange w1 s + defectChange w2 (runWord w1 s) := by
  unfold defectChange
  rw [runWord_append]
  ring

/-! ### Uniform defect change under iteration

If running `w` from each iterated state along the trajectory induces
the same defect change `c`, then `m` repetitions induce defect change
`m·c`. This is the formal core of S210 / S211. -/

theorem defectChange_repeat'_bounded (w : Word) (c : Int) (s : AdmState)
    (m : Nat)
    (h : ∀ k, k < m → defectChange w (runWord (Word.repeat' w k) s) = c) :
    defectChange (Word.repeat' w m) s = (m : Int) * c := by
  induction m with
  | zero => simp [Word.repeat', defectChange, runWord]
  | succ m ih =>
      have h_bounded : ∀ k, k < m →
          defectChange w (runWord (Word.repeat' w k) s) = c :=
        fun k hk => h k (Nat.lt_succ_of_lt hk)
      rw [Word.repeat'_succ, defectChange_append, ih h_bounded,
          h m (Nat.lt_succ_self m)]
      push_cast; ring

/-! ### S211.2 — Subcritical slope criterion

If a word `u` lands in the cylinder of a fixed-point word `w`, with
defect strictly below `m`, and `w` has uniform defect change `−1`
along the iterated trajectory, then `u w^m` is admissible with
`A < 2q`. -/

theorem S211_subcritical_criterion
    (u : Word) (w : Word) (m : Nat)
    (h_defect_below_m : defect (evalWord u) < (m : Int))
    (h_uniform : ∀ k, k < m →
        defectChange w (runWord (Word.repeat' w k) (evalWord u)) = -1) :
    defect (evalWord (u ++ Word.repeat' w m)) < 0 := by
  have h_concat :
      defect (evalWord (u ++ Word.repeat' w m))
        = defect (evalWord u) + defectChange (Word.repeat' w m) (evalWord u) := by
    show defect (runWord (u ++ Word.repeat' w m) initState)
       = defect (runWord u initState)
         + (defect (runWord (Word.repeat' w m) (runWord u initState))
            - defect (runWord u initState))
    rw [runWord_append]; ring
  have h_repeat :
      defectChange (Word.repeat' w m) (evalWord u) = (m : Int) * (-1) :=
    defectChange_repeat'_bounded w (-1) (evalWord u) m h_uniform
  rw [h_concat, h_repeat]
  have : ((m : Int) * (-1) : Int) = -(m : Int) := by ring
  rw [this]
  linarith

/-! ### Corollary: A < 2q from the criterion -/

/-- Bridge from `defect < 0` to `A < 2q` for any admissible run. -/
theorem A_lt_two_q_of_defect_neg (w : Word) (h : defect (evalWord w) < 0) :
    ((evalWord w).A : Int) < 2 * ((evalWord w).q : Int) := by
  unfold defect at h
  linarith

/-- Combined: under the S211 hypothesis, `A(u w^m) < 2·q(u w^m)`. -/
theorem S211_A_lt_two_q
    (u : Word) (w : Word) (m : Nat)
    (h_defect_below_m : defect (evalWord u) < (m : Int))
    (h_uniform : ∀ k, k < m →
        defectChange w (runWord (Word.repeat' w k) (evalWord u)) = -1) :
    ((evalWord (u ++ Word.repeat' w m)).A : Int)
      < 2 * ((evalWord (u ++ Word.repeat' w m)).q : Int) :=
  A_lt_two_q_of_defect_neg _
    (S211_subcritical_criterion u w m h_defect_below_m h_uniform)

end CollatzLean4.Admissible
