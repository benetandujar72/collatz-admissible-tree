/-
S214 — Local 3-adic potential framework for barrier certificates.

This module formalizes the abstract telescoping framework underlying
the S214 program: a path from `start` to a `goal` vertex in any
weighted directed graph has total weight at least `Φ(start) − Φ(goal)`,
provided Φ satisfies the local potential condition
`Φ(v) ≤ ω(v, v') + Φ(v')` along every edge.

Concrete instantiations (for the S202 inverse cylinder graph,
combining `ρ_+(c) = min(ν_3(c−1), h)` and `ρ_−(c) = min(ν_3(c+1), h)`
plus a finite local correction `ψ(c mod 3^h)`) are parameters: the
framework gives the implication "certificate ⇒ cost lower bound".

S214 CONJECTURE (NOT proven here):

  There exists a depth `h` and constants `λ, γ, μ > 0` such that the
  mixed potential

    Φ(j, c, r) = λ·δ_+(c, r) + γ·ρ_−(c, r) − μ(Q − j) + ψ(c mod 3^h)

  satisfies the local potential condition on the S202 inverse graph
  and yields `Φ(start) ≥ m` for all m large enough, hence
  `𝒞_{S202}^{←}(m, Q) ≥ m`.

This module supplies the framework theorem; closing the conjecture
requires constructing Φ explicitly (the S215 backward-search +
LP-feasibility computation).
-/

import CollatzLean4.Concatenation

namespace CollatzLean4.Admissible

/-! ### Generic weighted-graph telescoping framework -/

/-- Weighted path in a graph with `edge : V → V → Int → Prop`.
The path is a sequence of intermediate vertices with explicit
per-edge weights; total weight is the sum. -/
def WPath {V : Type} (edge : V → V → Int → Prop) :
    V → V → Int → List V → Prop
  | s, t, w, []       => s = t ∧ w = 0
  | s, t, w, v :: vs  =>
      ∃ ω₁ ω₂, edge s v ω₁ ∧ WPath edge v t ω₂ vs ∧ w = ω₁ + ω₂

/-- **S214 telescoping theorem** — abstract form.

If `Φ` is a *potential* (`Φ(v) ≤ ω + Φ(v')` on every edge), then any
path from `s` to `t` has weight ≥ `Φ(s) − Φ(t)`. -/
theorem WPath_weight_ge_potential
    {V : Type} (edge : V → V → Int → Prop) (Φ : V → Int)
    (h_pot : ∀ v v' ω, edge v v' ω → Φ v ≤ ω + Φ v') :
    ∀ {s t : V} {w : Int} {vs : List V},
      WPath edge s t w vs → Φ s - Φ t ≤ w := by
  intro s t w vs h_path
  induction vs generalizing s w with
  | nil =>
      simp [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      omega
  | cons v vs ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      have h1 : Φ s ≤ ω₁ + Φ v := h_pot _ _ _ h_edge
      have h2 : Φ v - Φ t ≤ ω₂ := ih h_rest
      linarith

/-! ### Barrier certificate via potential

If the potential is ≥ `m` at `start` and ≤ `0` at the goal, then any
path from `start` to a goal has weight ≥ `m`. -/

/-- Barrier corollary: `Φ(start) ≥ m` + `Φ(goal) ≤ 0` + potential
condition ⇒ every path from `start` to `goal` has weight ≥ `m`. -/
theorem barrier_from_potential
    {V : Type} (edge : V → V → Int → Prop) (Φ : V → Int)
    (h_pot : ∀ v v' ω, edge v v' ω → Φ v ≤ ω + Φ v')
    {start goal : V} (m : Int)
    (h_start : Φ start ≥ m)
    (h_goal : Φ goal ≤ 0)
    {w : Int} {vs : List V}
    (h_path : WPath edge start goal w vs) :
    m ≤ w := by
  have h := WPath_weight_ge_potential edge Φ h_pot h_path
  -- h : Φ start - Φ goal ≤ w
  -- Φ start ≥ m, Φ goal ≤ 0 ⇒ Φ start - Φ goal ≥ m
  -- ⇒ m ≤ w
  linarith

/-! ### Concrete potential ingredients (for documentation)

The S214 paper proposes a mixed potential combining:

  * δ_+(c, r) = r − min(ν_3(c − 1), r) — "distance to 1".
  * ρ_−(c, r) = min(ν_3(c + 1), r)     — "proximity to −1".
  * (Q − j)                            — "credit for remaining zeros".
  * ψ(c mod 3^h)                       — finite local correction.

In Lean, these are parameters of the abstract framework above:
specific choices instantiate `Φ : V → Int` and the user must
discharge the potential condition `h_pot`. This module does NOT
construct a specific Φ for the S202 inverse graph; that's the S215
content. -/

/-- Local 3-adic potential certificate (data interface). -/
structure LocalPotentialCertificate (V : Type) where
  /-- The potential function on the vertex space. -/
  Φ : V → Int
  /-- The edge predicate (typically: backward inverse-cylinder steps). -/
  edge : V → V → Int → Prop
  /-- Designated starting vertex (typically `[a_{S202}]_{R_m}`). -/
  start : V
  /-- Predicate identifying "goal" vertices (typically `[1]_r`). -/
  isGoal : V → Prop
  /-- Target barrier value (typically `m`). -/
  target : Int
  /-- Edge condition: potential is locally non-increasing along edges. -/
  edge_cond : ∀ v v' ω, edge v v' ω → Φ v ≤ ω + Φ v'
  /-- Goals have non-positive potential. -/
  goal_cond : ∀ v, isGoal v → Φ v ≤ 0
  /-- Starting potential meets the target. -/
  start_cond : Φ start ≥ target

/-- A certificate implies the cost lower bound: every admissible path
from `start` to any goal has weight ≥ `target`. -/
theorem LocalPotentialCertificate.barrier
    {V : Type} (cert : LocalPotentialCertificate V)
    {goal : V} (h_goal : cert.isGoal goal)
    {w : Int} {vs : List V}
    (h_path : WPath cert.edge cert.start goal w vs) :
    cert.target ≤ w :=
  barrier_from_potential cert.edge cert.Φ cert.edge_cond cert.target
    cert.start_cond (cert.goal_cond goal h_goal) h_path

end CollatzLean4.Admissible
