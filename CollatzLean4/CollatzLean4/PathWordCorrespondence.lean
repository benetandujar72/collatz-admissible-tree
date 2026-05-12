/-
S212 — Path-word correspondence (open conjecture) and the
closure-certificate framework (decidable facts).

This module:

1. **States S212 as a `Prop` conjecture.** Paths in the inverse cylinder
   graph from `InvStart m` to a goal correspond bijectively to
   admissible words `u` with `n(u) ≡ aS202 (mod 3^(22m+2))` and
   `D(u) =` path weight.

2. **Provides a `LiftedCertificate` interface** bundling the three
   decidable checks that a Python-emitted closure certificate
   satisfies. Each instance is a finite witness to a barrier on the
   *inverse-graph* side.

3. **Documents the gap.** Lifting a `LiftedCertificate` to a formal
   barrier theorem (`weight ≥ T` for every inverse-graph path from
   start to a goal) requires Bellman-Ford correctness — i.e., showing
   that the closure-invariant uniquely determines the minimum path
   weight from start. This is a standard result on weighted graphs;
   formalizing it from scratch in Lean would be substantial. The
   present module isolates the missing piece as a `Prop`.

If both S212 and the closure→barrier lemma are closed, then any
Python-generated certificate yields a formal Lean theorem of the form
`𝒞_{S202}(m) ≥ T`. Combined with `S211_S202_subcritical`, this yields
the `SlopeBarrier` case of the `S202_alternative_conjecture` for
bounded budgets.
-/

import CollatzLean4.InverseGraph
import CollatzLean4.Concatenation

namespace CollatzLean4.Admissible

/-! ### S212 — Path-word correspondence (CONJECTURE) -/

/-- **S212 conjecture**: paths from `InvStart m` to a goal in the
inverse cylinder graph correspond bijectively to admissible words
`u` with `n(u) ≡ aS202 (mod 3^(22m+2))`, with edge weights summing
to `defect (evalWord u)`.

Formally: for every admissible word `u` reaching the m-th cylinder,
the unfolding of `u` traces an inverse-graph path from `InvStart m`
to a goal vertex of weight equal to `D(u)`, and vice versa.

This is the structural identification that converts inverse-graph
barriers into admissible-word barriers. -/
def S212_path_word_correspondence (m : Nat) : Prop :=
  (∀ (u : Word),
      (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) →
      ∃ (vs : List InvVertex) (goal : InvVertex),
        InvVertex.IsGoal goal (22 * m + 2) ∧
        WPath (InvEdge (22 * m + 2)) (InvStart m) goal
              (defect (evalWord u)) vs)
  ∧
  (∀ (vs : List InvVertex) (goal : InvVertex) (w : Int),
      InvVertex.IsGoal goal (22 * m + 2) →
      WPath (InvEdge (22 * m + 2)) (InvStart m) goal w vs →
      ∃ (u : Word),
        (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) ∧
        defect (evalWord u) = w)

/-! ### Decidable closure-certificate interface

A `LiftedCertificate` packages three decidable facts about a finite
dist table: it satisfies the Bellman-Ford relaxation invariant
restricted to its visited region, contains no goal vertex with `dist
< T`, and has `start` with `dist = 0`. -/

/-- A closure-certificate lifted to Lean: the dist table plus the
three checks that compose its empirical validity. -/
structure LiftedCertificate (m Q T : Nat) where
  /-- The finite dist table. -/
  tbl : List (InvVertex × Int)
  /-- For every `(s, ds) ∈ tbl` with `ds < T`, every generated edge
  `(v, ω) ∈ outgoingEdges (22m+2) Q s` has `lookup tbl T v ≤ ds + ω`. -/
  closure_holds :
    tbl.all (fun ⟨s, ds⟩ =>
      (outgoingEdges (22 * m + 2) Q s).all (fun (e : InvVertex × Int) =>
        decide (((tbl.find? (·.1 = e.1)).map (·.2)).getD (T : Int)
                  ≤ ds + e.2))) = true
  /-- No `(v, d) ∈ tbl` with `d < T` is a goal at its cylinder modulus. -/
  no_goal_holds :
    tbl.all (fun (p : InvVertex × Int) =>
      let v := p.1; let d := p.2
      !decide (d < (T : Int)) ||
      !decide (v.c % (3 ^ (22 * m + 2 + v.j)) =
               1 % (3 ^ (22 * m + 2 + v.j)))) = true
  /-- The start vertex has dist `0` in the table. -/
  start_holds : ((tbl.find? (·.1 = InvStart m)).map (·.2)).getD (T : Int) = 0

/-! ### S216 — Closure-to-barrier (CONJECTURE)

A `LiftedCertificate` proves the empirical fact that no inverse-graph
path *staying inside the dist table* reaches a goal with weight `< T`.
Upgrading this to "no inverse-graph path *whatsoever* reaches a goal
with weight `< T`" requires Bellman-Ford correctness for the relaxed
dist labels — i.e., the claim that the relaxed dist labels are
LOWER BOUNDS on the true min-weight to each visited vertex.

This is a known graph-theory result; formalizing it cleanly in Lean
is the next step. -/

/-- Closure-to-barrier conjecture: a `LiftedCertificate` for `(m, Q, T)`
implies every inverse-graph path from `InvStart m` to a goal has
weight `≥ T`. -/
def S216_closure_to_barrier_conjecture (m Q T : Nat) : Prop :=
  LiftedCertificate m Q T →
    ∀ (vs : List InvVertex) (goal : InvVertex) (w : Int),
      InvVertex.IsGoal goal (22 * m + 2) →
      WPath (InvEdge (22 * m + 2)) (InvStart m) goal w vs →
      (T : Int) ≤ w

/-! ### Full chain (conditional on S212 + S216)

Combined: `S212` + `S216` + a `LiftedCertificate` yield a formal
barrier on admissible words: no `u` with `n(u) ≡ aS202 (mod 3^(22m+2))`
has `D(u) < T`. This is `𝒞_{S202}^(Q)(m) ≥ T`. -/

/-- Bundled barrier statement: under S212 and S216, a certificate
yields the admissible-word barrier. -/
theorem barrier_chain
    (m Q T : Nat)
    (h_S212 : S212_path_word_correspondence m)
    (h_S216 : S216_closure_to_barrier_conjecture m Q T)
    (cert : LiftedCertificate m Q T) :
    ∀ (u : Word),
      (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) →
      (T : Int) ≤ defect (evalWord u) := by
  intro u h_cyl
  obtain ⟨vs, goal, h_g, h_path⟩ := h_S212.1 u h_cyl
  exact h_S216 cert vs goal _ h_g h_path

end CollatzLean4.Admissible
