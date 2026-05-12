/-
S215 — Concrete inverse cylinder graph for S202 barriers.

Formalizes the inverse-cylinder graph used by the Python certificate
engine (`S202Engine`), so that a `closure_certificate` produced
externally can be lifted to a Lean theorem.

Vertices: pairs `(j, c)` where `j` is the number of inverse zero-steps
used and `c` is the cylinder representative residue.

Edges:
  * `InvEdgeOne` — inverse of `Branch.one`. Same `j`, weight `τ(α)`.
    From `(j, c)` to `(j, c')` with `c ≡ 2^τ · c' (mod 3^(R+j))`,
    where `α = c' mod 9` is admissible and `τ = τ(α)`.

  * `InvEdgeZero` — inverse of `Branch.zero`. `j ↦ j + 1`,
    weight `τ(α) − 2`. From `(j, c)` to `(j+1, c')` with
    `3c + 1 ≡ 2^τ · c' (mod 3^(R+j+1))`.

CONTENT:
  * `InvVertex`, `InvEdge`, `InvStart`, `InvVertex.IsGoal` — graph data.
  * `mkS202Cert` — package a candidate Φ + 3 conditions into a
    `LocalPotentialCertificate InvVertex`.
  * `S202_barrier_from_cert` — main barrier theorem: a valid certificate
    proves every inverse-graph path from `InvStart m` to a goal has
    total weight `≥ m`.

NOT proven here (the S212 correspondence): paths in the inverse graph
from `InvStart m` to a goal correspond bijectively to admissible
words `u` with `n(u) ≡ aS202 (mod 3^(22m+2))`. Adding this would
upgrade "inverse path cost ≥ m" to "admissible word defect ≥ m", at
which point the S211 concatenation `u · wS202^m` yields a formal
proof that `𝒞_{S202}(m) ≥ m`.
-/

import CollatzLean4.PotentialBarrier
import CollatzLean4.S202Cylinders

namespace CollatzLean4.Admissible

/-! ### Inverse-graph vertex space -/

/-- A vertex in the inverse cylinder graph: `j` = zero-steps used,
`c` = cylinder representative residue. -/
structure InvVertex where
  j : Nat
  c : Nat
deriving DecidableEq, Repr

namespace InvVertex

/-- Total cylinder precision: `R + j`. -/
@[inline] def precision (v : InvVertex) (R : Nat) : Nat := R + v.j

/-- The cylinder modulus: `3 ^ (R + j)`. -/
@[inline] def modulus (v : InvVertex) (R : Nat) : Nat := 3 ^ (R + v.j)

/-- Goal condition: the cylinder `[c]_{R+j}` contains the root `1`,
i.e., `c ≡ 1 (mod 3^(R+j))`. -/
def IsGoal (v : InvVertex) (R : Nat) : Prop :=
  v.c % (3 ^ (R + v.j)) = 1 % (3 ^ (R + v.j))

end InvVertex

/-! ### Edge predicates -/

/-- Inverse of `Branch.one`: from `(j, c)` to `(j, c')` with weight `τ(α)`.
Requires `c' mod 9 ∈ X` (admissible) and the forward consistency
`c ≡ 2^τ(c') · c' (mod 3^(R+j))`. -/
def InvEdgeOne (R : Nat) (v v' : InvVertex) (ω : Int) : Prop :=
  v'.j = v.j ∧
  InX v'.c ∧
  v.c % (3 ^ (R + v.j)) =
    (2 ^ tau v'.c * v'.c) % (3 ^ (R + v.j)) ∧
  ω = (tau v'.c : Int)

/-- Inverse of `Branch.zero`: from `(j, c)` to `(j+1, c')` with weight
`τ(c') − 2`. Requires `c' mod 9 ∈ X` and the forward consistency
`3c + 1 ≡ 2^τ(c') · c' (mod 3^(R+j+1))`. -/
def InvEdgeZero (R : Nat) (v v' : InvVertex) (ω : Int) : Prop :=
  v'.j = v.j + 1 ∧
  InX v'.c ∧
  (3 * v.c + 1) % (3 ^ (R + v'.j)) =
    (2 ^ tau v'.c * v'.c) % (3 ^ (R + v'.j)) ∧
  ω = (tau v'.c : Int) - 2

/-- Combined inverse edge: either a `one` or a `zero` inverse step. -/
def InvEdge (R : Nat) (v v' : InvVertex) (ω : Int) : Prop :=
  InvEdgeOne R v v' ω ∨ InvEdgeZero R v v' ω

/-- Starting vertex for the m-th S202 cylinder: `j = 0` and
`c = aS202 mod 3^(22m+2)`. -/
def InvStart (m : Nat) : InvVertex :=
  ⟨0, aS202 % (3 ^ (22 * m + 2))⟩

/-! ### Barrier certificate plumbing -/

/-- Construct a `LocalPotentialCertificate` for the m-th S202 cylinder
barrier from a candidate potential `Φ` plus the three conditions:
edge-monotonicity, goal non-positivity, start lower bound. -/
def mkS202Cert (m : Nat) (Φ : InvVertex → Int)
    (h_edge : ∀ v v' ω,
      InvEdge (22 * m + 2) v v' ω → Φ v ≤ ω + Φ v')
    (h_goal : ∀ v,
      InvVertex.IsGoal v (22 * m + 2) → Φ v ≤ 0)
    (h_start : Φ (InvStart m) ≥ (m : Int)) :
    LocalPotentialCertificate InvVertex :=
{ Φ := Φ
  edge := InvEdge (22 * m + 2)
  start := InvStart m
  isGoal := fun v => InvVertex.IsGoal v (22 * m + 2)
  target := (m : Int)
  edge_cond := h_edge
  goal_cond := h_goal
  start_cond := h_start }

/-- **S215 barrier theorem**: a valid potential certificate for the
m-th S202 cylinder proves that every inverse-graph path from
`InvStart m` to a goal vertex has total weight at least `m`. -/
theorem S202_barrier_from_cert (m : Nat) (Φ : InvVertex → Int)
    (h_edge : ∀ v v' ω,
      InvEdge (22 * m + 2) v v' ω → Φ v ≤ ω + Φ v')
    (h_goal : ∀ v,
      InvVertex.IsGoal v (22 * m + 2) → Φ v ≤ 0)
    (h_start : Φ (InvStart m) ≥ (m : Int))
    {goal : InvVertex} (h_g : InvVertex.IsGoal goal (22 * m + 2))
    {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge (22 * m + 2)) (InvStart m) goal w vs) :
    (m : Int) ≤ w :=
  (mkS202Cert m Φ h_edge h_goal h_start).barrier h_g h_path

/-! ### Computable edge generator

Concrete enumeration of outgoing inverse-edges from a vertex. Uses
the closed-form inverse `(M+1)/2` of `2` modulo odd `M = 3^k`. -/

/-- Inverse of `2` modulo an odd `M`: `(M+1)/2`. -/
@[inline] def invMod2 (M : Nat) : Nat := (M + 1) / 2

/-- Inverse of `2^τ` modulo an odd `M`. -/
@[inline] def invMod2Pow (τ M : Nat) : Nat := (invMod2 M) ^ τ % M

/-- Generated inverse-edges from vertex `v` at base precision `R` with
zero-budget `Q`. Matches the Python `S202Engine.outgoing_edges`:
  * one-edges always generated.
  * zero-edges only when `v.j < Q` (budget not exhausted).
-/
def outgoingEdges (R Q : Nat) (v : InvVertex) : List (InvVertex × Int) :=
  let oneEdges :=
    let M := 3 ^ (R + v.j)
    [1, 2, 4, 5, 7, 8].filterMap (fun α =>
      let τ := tau α
      let y := invMod2Pow τ M * v.c % M
      if y % 9 = α then some (⟨v.j, y⟩, (τ : Int)) else none)
  let zeroEdges :=
    if v.j < Q then
      let M' := 3 ^ (R + v.j + 1)
      [1, 2, 4, 5, 7, 8].filterMap (fun α =>
        let τ := tau α
        let y := invMod2Pow τ M' * (3 * v.c + 1) % M'
        if y % 9 = α then some (⟨v.j + 1, y⟩, (τ : Int) - 2) else none)
    else []
  oneEdges ++ zeroEdges

/-! ### Trivial m = 0 case

For m = 0, the cylinder is `[aS202]_9`, and `aS202 mod 9 = 1`, so
`InvStart 0 = ⟨0, 1⟩` is itself a goal vertex. Any path from start
to goal has weight `≥ 0` (taking `Φ ≡ 0` as the trivial potential
certifies this). -/

theorem InvStart_zero_isGoal : InvVertex.IsGoal (InvStart 0) 2 := by
  show (InvStart 0).c % (3 ^ (2 + (InvStart 0).j))
       = 1 % (3 ^ (2 + (InvStart 0).j))
  show (aS202 % (3 ^ (22 * 0 + 2))) % (3 ^ (2 + 0))
       = 1 % (3 ^ (2 + 0))
  -- aS202 mod 9 = 1
  simp [S206_a_mod9]

end CollatzLean4.Admissible
