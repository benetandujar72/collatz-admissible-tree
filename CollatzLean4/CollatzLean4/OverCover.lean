/-
S215 — Over-cover theorem.

Generic meta-theorem: if `(V_a, aEdge)` over-covers `(V_c, cEdge)` via
an abstraction map `α : V_c → V_a` (every concrete edge has an abstract
counterpart of weight ≤), then:

  * any abstract potential lifts to a concrete potential;
  * any concrete weighted path induces an abstract one of weight ≤;
  * any abstract barrier certificate yields a concrete barrier.

Concrete payoff for S202: the abstraction `α_h(j, c) = (j, c mod 3^h)`
collapses the concrete inverse cylinder graph to a finite quotient
indexed by `(j, c mod 3^h)`. A potential table on the quotient
certifies the same barrier on the original graph, but is
exponentially smaller. The threshold `h ≥ 23` is required to
distinguish `aS202` from `1` — see `aS202_ne_one_mod_3_pow_23` in
`Potential.lean`.

This module supplies the *meta-theorem*. Constructing a specific
abstract potential `Φ_a` that satisfies the local condition on the
abstract graph and yields `Φ_a(α (InvStart m)) ≥ m` is the open
problem (S214/S215 conjecture).
-/

import CollatzLean4.PotentialBarrier
import CollatzLean4.InverseGraph
import CollatzLean4.Potential

namespace CollatzLean4.Admissible

/-! ### Generic over-cover framework -/

/-- An **over-cover** of a concrete weighted graph `(V_c, cEdge)` by an
abstract weighted graph `(V_a, aEdge)`: an abstraction map
`α : V_c → V_a` such that every concrete edge `cEdge v v' ω` is
witnessed by an abstract edge `aEdge (α v) (α v') ω'` with `ω' ≤ ω`. -/
structure OverCover (V_c V_a : Type)
    (cEdge : V_c → V_c → Int → Prop)
    (aEdge : V_a → V_a → Int → Prop) where
  /-- Abstraction map. -/
  α : V_c → V_a
  /-- Covering condition: every concrete edge has an abstract
  counterpart of weight ≤. -/
  covers : ∀ v v' ω, cEdge v v' ω →
    ∃ ω', ω' ≤ ω ∧ aEdge (α v) (α v') ω'

namespace OverCover

variable {V_c V_a : Type}
  {cEdge : V_c → V_c → Int → Prop}
  {aEdge : V_a → V_a → Int → Prop}

/-- Lift an abstract potential to a concrete potential by composition
with the abstraction map. The local potential condition is preserved
because the over-cover provides an abstract edge of weight `≤` for
each concrete edge. -/
theorem lift_potential
    (cov : OverCover V_c V_a cEdge aEdge)
    (Φ_a : V_a → Int)
    (h_pot_a : ∀ v v' ω, aEdge v v' ω → Φ_a v ≤ ω + Φ_a v') :
    ∀ v v' ω, cEdge v v' ω →
      Φ_a (cov.α v) ≤ ω + Φ_a (cov.α v') := by
  intro v v' ω h_edge
  obtain ⟨ω', hω, h_aedge⟩ := cov.covers v v' ω h_edge
  have h := h_pot_a (cov.α v) (cov.α v') ω' h_aedge
  linarith

/-- Lift a concrete weighted path to an abstract weighted path of
total weight `≤`. The abstract path lives in the image of `α`. -/
theorem lift_path
    (cov : OverCover V_c V_a cEdge aEdge)
    {s t : V_c} {w : Int} {vs : List V_c}
    (h_path : WPath cEdge s t w vs) :
    ∃ (w' : Int) (vs' : List V_a),
      w' ≤ w ∧ WPath aEdge (cov.α s) (cov.α t) w' vs' := by
  induction vs generalizing s w with
  | nil =>
      simp [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      refine ⟨0, [], le_refl 0, ?_⟩
      simp [WPath]
  | cons v vs ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      obtain ⟨ω₁', hω₁', h_aedge⟩ := cov.covers s v ω₁ h_edge
      obtain ⟨w', vs', hw', h_apath⟩ := ih h_rest
      refine ⟨ω₁' + w', cov.α v :: vs', by linarith, ?_⟩
      simp only [WPath]
      exact ⟨ω₁', w', h_aedge, h_apath, rfl⟩

/-- **S215 over-cover barrier theorem** — abstract form.

An abstract potential satisfying the local condition on `(V_a, aEdge)`
yields a concrete barrier on `(V_c, cEdge)` via the abstraction map:
any concrete path from `start` to a goal vertex has total weight
`≥ target`. -/
theorem barrier
    (cov : OverCover V_c V_a cEdge aEdge)
    (Φ_a : V_a → Int)
    (h_pot_a : ∀ v v' ω, aEdge v v' ω → Φ_a v ≤ ω + Φ_a v')
    {start : V_c} {isGoal_c : V_c → Prop}
    (target : Int)
    (h_start : Φ_a (cov.α start) ≥ target)
    (h_goal : ∀ v, isGoal_c v → Φ_a (cov.α v) ≤ 0)
    {goal : V_c} (h_g : isGoal_c goal)
    {w : Int} {vs : List V_c}
    (h_path : WPath cEdge start goal w vs) :
    target ≤ w :=
  barrier_from_potential cEdge (Φ_a ∘ cov.α)
    (cov.lift_potential Φ_a h_pot_a)
    target h_start (h_goal goal h_g) h_path

/-- Over-cover applied to a packaged abstract certificate. Given a
`LocalPotentialCertificate V_a` whose `edge = aEdge` and whose goal
predicate is consistent with the concrete goals through `α`, we get a
concrete barrier of weight `≥ cert.target`. -/
theorem from_abstract_certificate
    (cov : OverCover V_c V_a cEdge aEdge)
    (acert : LocalPotentialCertificate V_a)
    (h_aedge : acert.edge = aEdge)
    {start_c : V_c} {isGoal_c : V_c → Prop}
    (h_start : cov.α start_c = acert.start)
    (h_goal : ∀ v, isGoal_c v → acert.isGoal (cov.α v))
    {goal : V_c} (h_g : isGoal_c goal)
    {w : Int} {vs : List V_c}
    (h_path : WPath cEdge start_c goal w vs) :
    acert.target ≤ w := by
  apply cov.barrier acert.Φ ?_ acert.target ?_ ?_ h_g h_path
  · intro v v' ω h_ae
    apply acert.edge_cond v v' ω
    rw [h_aedge]; exact h_ae
  · rw [h_start]; exact acert.start_cond
  · intro v h_gv
    exact acert.goal_cond _ (h_goal v h_gv)

end OverCover

/-! ### Canonical S202 abstraction: `(j, c mod 3^h)`

For `h ≥ 23`, this distinguishes `aS202` from `1` (see
`aS202_ne_one_mod_3_pow_23` in `Potential.lean`). For `h ≤ 22`,
the abstraction collapses the start vertex `InvStart m` with any
goal at low precision, so barriers above `0` cannot be established. -/

/-- The canonical abstraction map for the S202 inverse graph. -/
def S202Abstraction (h : Nat) (v : InvVertex) : Nat × Nat :=
  (v.j, v.c % 3 ^ h)

/-- Induced abstract edge relation: a quotient-graph edge exists iff
some concrete edge between vertices in the corresponding fibres
exists. Always satisfies the over-cover condition. -/
def InducedAbsEdge (R h : Nat) (v_a v_a' : Nat × Nat) (ω : Int) : Prop :=
  ∃ v v' : InvVertex,
    S202Abstraction h v = v_a ∧
    S202Abstraction h v' = v_a' ∧
    InvEdge R v v' ω

/-- The induced abstraction is an over-cover by construction. -/
def s202OverCover_induced (R h : Nat) :
    OverCover InvVertex (Nat × Nat) (InvEdge R) (InducedAbsEdge R h) :=
{ α := S202Abstraction h
  covers := fun v v' ω h_e =>
    ⟨ω, le_refl ω, v, v', rfl, rfl, h_e⟩ }

/-! ### S215 barrier corollary for the S202 inverse graph -/

/-- **S215 barrier corollary**: an over-cover of the m-th S202 inverse
cylinder graph plus an abstract potential certificate yields the
cylinder barrier `𝒞^←_{S202}(m) ≥ target`: every inverse-graph path
from `InvStart m` to a goal vertex has total weight `≥ target`. -/
theorem S202_barrier_from_overcover (m : Nat)
    {V_a : Type} {aEdge : V_a → V_a → Int → Prop}
    (cov : OverCover InvVertex V_a (InvEdge (22 * m + 2)) aEdge)
    (Φ_a : V_a → Int)
    (h_pot_a : ∀ v v' ω, aEdge v v' ω → Φ_a v ≤ ω + Φ_a v')
    (target : Int)
    (h_start : Φ_a (cov.α (InvStart m)) ≥ target)
    (h_goal : ∀ v, InvVertex.IsGoal v (22 * m + 2) → Φ_a (cov.α v) ≤ 0)
    {goal : InvVertex} (h_g : InvVertex.IsGoal goal (22 * m + 2))
    {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge (22 * m + 2)) (InvStart m) goal w vs) :
    target ≤ w :=
  cov.barrier Φ_a h_pot_a target h_start h_goal h_g h_path

/-! ### Sanity: the trivial over-cover by identity is consistent

`α = id` from `(V_c, cEdge)` to itself is always an over-cover, and
the resulting barrier reduces to the concrete `barrier_from_potential`.
This confirms the abstract framework subsumes the concrete one. -/

/-- Identity over-cover: trivially exists. -/
def OverCover.id {V : Type} (edge : V → V → Int → Prop) :
    OverCover V V edge edge :=
{ α := fun v => v
  covers := fun _ _ ω h_e => ⟨ω, le_refl ω, h_e⟩ }

/-- The identity over-cover gives back the original barrier theorem. -/
theorem OverCover.id_barrier {V : Type}
    (edge : V → V → Int → Prop) (Φ : V → Int)
    (h_pot : ∀ v v' ω, edge v v' ω → Φ v ≤ ω + Φ v')
    {start : V} {isGoal : V → Prop}
    (target : Int)
    (h_start : Φ start ≥ target)
    (h_goal : ∀ v, isGoal v → Φ v ≤ 0)
    {goal : V} (h_g : isGoal goal)
    {w : Int} {vs : List V}
    (h_path : WPath edge start goal w vs) :
    target ≤ w :=
  (OverCover.id edge).barrier Φ h_pot target h_start h_goal h_g h_path

end CollatzLean4.Admissible
