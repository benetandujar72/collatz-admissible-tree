/-
Computational reachability for `InImageTheta`.

For specific small `n ∈ X` we certify `InImageTheta n` by exhibiting
an explicit word `w` with `(evalWord w).n = n`, verified by `native_decide`.

This module also provides:

  * `findWitness d target` — a depth-bounded DFS returning `Option Word`,
    intended as a discovery tool. Soundness is not proven formally; use
    the explicit-witness theorems below for verified statements.

  * `reachableWithin d target s` — a Bool-valued reachability check
    (depth ≤ d from state s). `decide` and `native_decide` work directly
    on its evaluation.

NOTE: this module does NOT close the Collatz-equivalent claim
`∀ n ∈ X, InImageTheta n` — that is exactly the open problem.

Empirical observation: not every `n ∈ X` is reachable. The model maps
`n = 1` forward via specific τ-grouped doublings; small values like
`n = 2`, `n = 8` are NOT reached within depth 12, while their residue
classes mod 9 are (e.g. `n = 11 ≡ 2` and `n = 17 ≡ 8` ARE reached).
This is a structural restriction of the τ-table, not an open question:
no `s` with `s.n ∈ X` and the prescribed τ produces `step s b = 2` or
`= 8` directly (see commentary below).
-/

import CollatzLean4.TranslationSets

namespace CollatzLean4.Admissible

/-! ### Bounded DFS (discovery tool) -/

/-- Depth-bounded DFS for a word `w` with `(runWord w s).n = target`.
Tries `Branch.zero` first, then `Branch.one`. -/
def findWitnessAux : Nat → Nat → AdmState → Option Word
  | 0,     target, s => if s.n = target then some [] else none
  | (d+1), target, s =>
      if s.n = target then some []
      else
        match findWitnessAux d target (step s Branch.zero) with
        | some w => some (Branch.zero :: w)
        | none =>
            match findWitnessAux d target (step s Branch.one) with
            | some w => some (Branch.one :: w)
            | none => none

/-- Search for a witness to `InImageTheta target` from `initState`. -/
def findWitness (d target : Nat) : Option Word :=
  findWitnessAux d target initState

/-! ### Decidable reachability (Bool form) -/

/-- `true` iff some word of length ≤ d from `s` reaches the target. -/
def reachableWithin : Nat → Nat → AdmState → Bool
  | 0,     target, s => decide (s.n = target)
  | (d+1), target, s =>
      decide (s.n = target) ||
      reachableWithin d target (step s Branch.zero) ||
      reachableWithin d target (step s Branch.one)

/-! ### Explicit verified witnesses

Each theorem provides an explicit word with `native_decide` checking
the evaluation. The witness is the actual admissible inverse trajectory
from 1 to the target. -/

theorem InImageTheta_one : InImageTheta 1 := ⟨[], rfl⟩

theorem InImageTheta_four : InImageTheta 4 :=
  ⟨[Branch.one], by native_decide⟩

theorem InImageTheta_five : InImageTheta 5 :=
  ⟨[Branch.one, Branch.zero], by native_decide⟩

theorem InImageTheta_thirteen : InImageTheta 13 :=
  ⟨[Branch.one, Branch.zero, Branch.zero], by native_decide⟩

theorem InImageTheta_sixteen : InImageTheta 16 :=
  ⟨[Branch.one, Branch.one], by native_decide⟩

theorem InImageTheta_seventeen : InImageTheta 17 :=
  ⟨[Branch.one, Branch.zero, Branch.zero, Branch.zero], by native_decide⟩

theorem InImageTheta_forty : InImageTheta 40 :=
  ⟨[Branch.one, Branch.zero, Branch.one], by native_decide⟩

theorem InImageTheta_eleven : InImageTheta 11 :=
  ⟨[Branch.one, Branch.zero, Branch.zero, Branch.zero, Branch.zero],
    by native_decide⟩

/-! ### Empirical: `reachableWithin` for small targets

For values reachable: the Bool check returns `true`. For `n = 2, 8` it
returns `false` even at depth 12 — empirical evidence of structural
non-reachability. -/

theorem reachable_one_within_12 : reachableWithin 12 1 initState = true := by
  native_decide

theorem reachable_four_within_12 : reachableWithin 12 4 initState = true := by
  native_decide

theorem reachable_eleven_within_12 : reachableWithin 12 11 initState = true := by
  native_decide

theorem reachable_seventeen_within_12 : reachableWithin 12 17 initState = true := by
  native_decide

/-- **Structural observation**: `n = 2` is not reached by any word of
length ≤ 12 starting from `initState`. (Not a non-reachability proof —
that would require an inductive invariant.) -/
theorem no_short_path_to_two :
    reachableWithin 12 2 initState = false := by native_decide

/-- Same for `n = 8`. -/
theorem no_short_path_to_eight :
    reachableWithin 12 8 initState = false := by native_decide

/-! ### Why `n = 2` is structurally unreachable (sketch, not formalized)

For `Branch.one`: `(step s one).n = 2^τ(s.n) · s.n = 2` requires `τ = 1`
and `s.n = 1`, but `τ(1) = 2`. So no admissible `s` yields `step s one = 2`.

For `Branch.zero`: `(step s zero).n = (2^τ s.n − 1)/3 = 2` requires
`2^τ · s.n = 7`. Across `s.n mod 9 ∈ X` with the prescribed `τ`, the
products `{4, 4, 16, 40, 112, 16}` never include 7. So no admissible
`s` yields `step s zero = 2` either.

By induction, `2` is unreachable from `initState`. The same argument
applies to `8` (with `2^τ s.n = 25`, no solution in X).

Formalizing this requires either a finite-residue invariant or an
exhaustive ground enumeration; we leave both open for future work. -/

end CollatzLean4.Admissible
