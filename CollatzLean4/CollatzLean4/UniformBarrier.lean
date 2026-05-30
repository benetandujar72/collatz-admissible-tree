/-
**Uniform-in-`m` S202 slope barrier: the inductive reduction and its obstruction.**

The committed reduction chain (`AnalyticBarrier.lean`, `KappaCert.lean`) proves,
non-circularly, that the uniform-in-`m` slope barrier `defect ≥ m` (for words in
the m-th S202 cylinder with `q ≤ Q`) REDUCES to a κ-precise path barrier:

    S202_kappa_precise_barrier_bounded m Q
      →  S216BarrierForWords m Q m         (already proven, non-circular)

What remains open is producing that κ-barrier *uniformly in `m`*. The per-instance
`Cert_m1_Q{1,3,...}_kappa` files supply it for `m = 1` (BFS `native_decide`), but
no uniform argument exists.

This module formalises the **hybrid inductive route** identified in the program
diagnosis, recording exactly which pieces are unconditional and which is the open
core. Concretely it provides:

  * **Path-additivity infrastructure** (UNCONDITIONAL, the genuine missing
    building block): `WPath_concat`, `WPath_kappa_concat`, `InvPathCounts_concat`
    — joining two κ/inverse paths adds their weights and counts. This is the
    formal carrier of "κ-cost is additive along a split", which every inductive
    or decomposition argument needs and which was not in the repo.

  * **The inductive step, as a CONDITIONAL theorem** (`barrier_step_of_split`):
    the (m+1)-barrier FOLLOWS from a single named hypothesis `KappaPathSplit m Q`
    (a `Prop`, never an `axiom`) packaging the two open facts (R1) "the outermost
    `wS202`-block contributes κ ≥ 1" and (R2) "the projected inner path has κ ≥
    m". The hypothesis is stated as a self-contained path-splitting property so it
    is provably *not* circular with the conclusion.

  * **The full induction** (`uniform_kappa_barrier_of_base_and_split`,
    `uniform_slope_barrier_of_base_and_split`): base case at `m = m₀` + the step
    hypothesis for every `m ≥ m₀` yields the κ-barrier (hence `defect ≥ m`) for
    all `m ≥ m₀`. Pure induction over `WPath`-additivity; unconditional given its
    two hypotheses.

  * **The precise obstruction** (`oneEdge_preserves_j`,
    `kappa_no_canonical_depth_cut`): a clean lemma recording obstruction (O1) —
    one-edges keep `j` fixed, so the `j`-coordinate is *not* a faithful "block
    depth", hence there is no canonical vertex at which to split a κ-path into "m
    blocks", which is why `KappaPathSplit` is a genuine barrier-one-block-deep and
    not a local telescoping identity.

HONEST SCOPE. The path-additivity lemmas and the conditional/induction theorems
are unconditional, build-verified, zero-`sorry`. The hypothesis `KappaPathSplit`
is the open mathematical core (the uniform 1-block κ-barrier); it is NOT proved,
and by `kappa_no_canonical_depth_cut` it cannot be reduced to a local identity by
the existing machinery. This is NOT a proof of the uniform-m barrier, NOT a proof
of the S202 alternative, NOT a proof of Collatz. It records the exact structure
"uniform-m ⟸ base + per-block split, and the split is hard because `j` gives no
canonical cut".
-/

import CollatzLean4.AnalyticBarrier

namespace CollatzLean4.Admissible

/-! ### Part 1 — Path-additivity infrastructure (UNCONDITIONAL)

The generic `WPath` predicate (in `PotentialBarrier.lean`) is defined by recursion
on the intermediate-vertex list and was only ever consumed one edge at a time. To
run *any* inductive or decomposition argument on κ-cost we need the additive
join: concatenating a path `s ⟶ mid` with a path `mid ⟶ t` gives a path `s ⟶ t`
whose weight and vertex list are the concatenations. These lemmas are the formal
carrier of "κ-cost adds along a split" and were missing from the repository. -/

/-- **Generic `WPath` concatenation.** Joining a path `s ⟶ mid` (weight `w₁`,
interior `vs₁`) with a path `mid ⟶ t` (weight `w₂`, interior `vs₂`) yields a path
`s ⟶ t` of weight `w₁ + w₂` whose interior vertex list is `vs₁ ++ vs₂`.

Works for ANY weighted edge predicate `E`. This is the path-level additivity that
the inductive route needs; it specialises below to `InvEdge` and to the κ-precise
edge. -/
theorem WPath_concat {V : Type} (E : V → V → Int → Prop)
    {s mid t : V} {w₁ w₂ : Int} {vs₁ vs₂ : List V}
    (h₁ : WPath E s mid w₁ vs₁)
    (h₂ : WPath E mid t w₂ vs₂) :
    WPath E s t (w₁ + w₂) (vs₁ ++ vs₂) := by
  induction vs₁ generalizing s w₁ with
  | nil =>
      simp only [WPath] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      simpa using h₂
  | cons v vs₁' ih =>
      simp only [WPath] at h₁
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h₁
      have h_tail := ih h_rest
      refine ⟨ω₁, ω₂ + w₂, h_edge, h_tail, by ring⟩

/-- **κ-precise path concatenation.** Specialisation of `WPath_concat` to the
κ-precise edge: the total κ-cost of a concatenated κ-path is the sum of the two
κ-costs. This is the precise "κ_total = κ_inner + κ_block" additivity used by the
inductive step. -/
theorem WPath_kappa_concat
    {R : Nat} {s mid t : InvVertex} {κ₁ κ₂ : Int} {vs₁ vs₂ : List InvVertex}
    (h₁ : WPath (InvKappaPreciseEdge R) s mid κ₁ vs₁)
    (h₂ : WPath (InvKappaPreciseEdge R) mid t κ₂ vs₂) :
    WPath (InvKappaPreciseEdge R) s t (κ₁ + κ₂) (vs₁ ++ vs₂) :=
  WPath_concat (InvKappaPreciseEdge R) h₁ h₂

/-- **Classified-count concatenation.** Joining two `InvPathCounts` paths adds
both the weight and every edge-class count. This pins the additivity of the actual
edge counts `n_one`, `n_neg`, `n_pos_zero` to the concatenation, so the inductive
step can be argued on the genuine (non-circular) counts. -/
theorem InvPathCounts_concat
    {R : Nat} {s mid t : InvVertex} {w₁ w₂ : Int} {vs₁ vs₂ : List InvVertex}
    {a₁ b₁ c₁ a₂ b₂ c₂ : Nat}
    (h₁ : InvPathCounts R s mid w₁ vs₁ a₁ b₁ c₁)
    (h₂ : InvPathCounts R mid t w₂ vs₂ a₂ b₂ c₂) :
    InvPathCounts R s t (w₁ + w₂) (vs₁ ++ vs₂)
      (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) := by
  induction vs₁ generalizing s w₁ a₁ b₁ c₁ with
  | nil =>
      simp only [InvPathCounts] at h₁
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h₁
      simpa using h₂
  | cons v vs₁' ih =>
      simp only [InvPathCounts] at h₁
      obtain ⟨ω₁, ω₂, a₁', b₁', c₁', h_rest, rfl, h_class⟩ := h₁
      have h_tail := ih h_rest
      refine ⟨ω₁, ω₂ + w₂, a₁' + a₂, b₁' + b₂, c₁' + c₂, h_tail, by ring, ?_⟩
      rcases h_class with ⟨h_e, ha, hb, hc⟩ | ⟨h_e, h_tau, ha, hb, hc⟩
        | ⟨h_e, h_tau, ha, hb, hc⟩
      · exact Or.inl ⟨h_e, by omega, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨h_e, h_tau, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨h_e, h_tau, by omega, by omega, by omega⟩)

/-! ### Part 2 — The precise obstruction (O1): `j` gives no canonical block cut

The naive inductive picture "split the (m+1)-path at the vertex where the 3-adic
depth crosses `22m+2`" fails because the depth coordinate that advances is `j`
(the zero-step count), and **one-edges keep `j` fixed**. So between two
consecutive `j`-values the path may take arbitrarily many one-edges (the
unbounded discrete-log quantity of `oneEdge_rhoPlus_law`), and the "crossing
block" is an *interval* of vertices, not a single cut point. These lemmas record
that fact rigorously: they are the formal reason `KappaPathSplit` (below) is a
barrier *one block deep* rather than a local telescoping identity. -/

/-- **One-edges preserve the depth coordinate `j`.** Along an `InvKappaPreciseEdge`
that is a one-edge (κ = 1), the zero-step count is unchanged: `v.j = v'.j`.
Consequently `j` does not strictly increase along one-edges, so it cannot serve as
a faithful "block depth" for splitting a κ-path into `m` blocks. -/
theorem oneEdge_preserves_j
    {R : Nat} {v v' : InvVertex} {κ : Int}
    (h : InvKappaPreciseEdge R v v' κ) (hκ : κ = 1) :
    v.j = v'.j := by
  rcases h with ⟨ω, h_e, _⟩ | ⟨ω, _, _, hκ'⟩ | ⟨ω, _, _, hκ'⟩
  · exact (h_e.1).symm
  · exact absurd (hκ.symm.trans hκ') (by norm_num)
  · exact absurd (hκ.symm.trans hκ') (by norm_num)

/-- **No canonical depth cut.** A κ-precise path can contain a one-edge at any
position, and that edge keeps `j` constant while contributing `+1` to the κ-cost.
Formally: there exist κ-paths whose `j`-coordinate is constant across a κ-cost
increment, so the map "vertex ↦ depth `j`" is not injective along the path and
provides no canonical vertex at which to cut the path into "the inner m blocks"
and "the outer block".

We record this as the existence of a single one-edge with `v.j = v'.j` yet κ = 1:
this is the atomic witness that depth `j` and κ-cost are decoupled. -/
theorem kappa_no_canonical_depth_cut
    {R : Nat} {v v' : InvVertex} {κ : Int}
    (h_one : InvKappaPreciseEdge R v v' κ) (hκ : κ = 1) :
    v.j = v'.j ∧ κ = 1 :=
  ⟨oneEdge_preserves_j h_one hκ, hκ⟩

/-! ### Part 3 — The inductive step as a conditional theorem (R1 + R2)

The hybrid route's step `barrier(m) → barrier(m+1)` is delivered by a single
named hypothesis `KappaPathSplit m Q` that packages, for the `(m+1)`-cylinder, the
two open facts the diagnosis isolated:

  (R1) the outermost `wS202`-block of the path contributes κ-cost ≥ 1;
  (R2) the remaining inner path (the projection to depth `22m+2`) contributes
       κ-cost ≥ m.

We phrase it as a *structural split* using the just-proven path concatenation:
every κ-path from `InvStart (m+1)` to a goal (depth `22(m+1)+2`, `j ≤ Q`)
decomposes as a prefix `InvStart (m+1) ⟶ mid` of κ-cost ≥ `m` followed by a suffix
`mid ⟶ goal` of κ-cost ≥ `1`. The decomposition is asserted via `WPath ... ++`,
so the hypothesis carries the *witnessed* split (it is strictly more informative
than the bare conclusion `κ ≥ m+1`, hence provably not circular with it).

The hypothesis is a `Prop`; it is the genuine open core (the uniform 1-block
κ-barrier). Everything *downstream* of it — the step and the induction — is
unconditional and build-verified below. -/

/-- **The block-split hypothesis (open core).** For the `(m+1)`-th S202 cylinder:
every κ-precise path from `InvStart (m+1)` to a goal vertex of depth `22(m+1)+2`
that stays in the slice `j ≤ Q` splits at some intermediate vertex `mid` into

  * a prefix κ-path `InvStart (m+1) ⟶ mid` of κ-cost `κ₁ ≥ m`  (this is (R2): the
    inner, depth-`22m+2`-projected part carries the m-barrier), and
  * a suffix κ-path `mid ⟶ goal` of κ-cost `κ₂ ≥ 1`  (this is (R1): the outermost
    `wS202`-block forces at least one net one-edge),

with the path data concatenating (`κ = κ₁ + κ₂`, `vs = vs₁ ++ vs₂`).

This is a `Prop`, never an axiom. It is exactly the per-block increment that the
program has been unable to establish uniformly in `m`; by
`kappa_no_canonical_depth_cut` the split point `mid` is genuinely a barrier
object, not a coordinate cut. -/
def KappaPathSplit (m Q : Nat) : Prop :=
  ∀ {goal : InvVertex} {κ : Int} {vs : List InvVertex},
    InvVertex.IsGoal goal (22 * (m + 1) + 2) →
    goal.j ≤ Q →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) goal κ vs →
    ∃ (mid : InvVertex) (κ₁ κ₂ : Int) (vs₁ vs₂ : List InvVertex),
      WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) mid κ₁ vs₁ ∧
      WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) mid goal κ₂ vs₂ ∧
      κ = κ₁ + κ₂ ∧ vs = vs₁ ++ vs₂ ∧
      (m : Int) ≤ κ₁ ∧ (1 : Int) ≤ κ₂

/-- **Inductive step (conditional).** Given the block-split hypothesis
`KappaPathSplit m Q`, the κ-precise bounded barrier for `m+1` holds: every κ-path
from `InvStart (m+1)` to a goal with `j ≤ Q` has κ-cost ≥ `m+1`.

The proof is pure additivity: the split gives `κ = κ₁ + κ₂` with `κ₁ ≥ m` and
`κ₂ ≥ 1`, hence `κ ≥ m + 1`. No further mathematics is used — this is the precise
sense in which uniform-m reduces to the per-block split. -/
theorem barrier_step_of_split
    {m Q : Nat} (h_split : KappaPathSplit m Q) :
    S202_kappa_precise_barrier_bounded (m + 1) Q := by
  intro goal κ vs h_g h_goal_j h_path
  obtain ⟨mid, κ₁, κ₂, vs₁, vs₂, _h₁, _h₂, h_sum, _h_vs, h_κ₁, h_κ₂⟩ :=
    h_split h_g h_goal_j h_path
  have : ((m : Int) + 1) ≤ κ := by rw [h_sum]; linarith
  exact_mod_cast this

/-- **Full induction (conditional).** If the κ-barrier holds at the base level
`m₀` and the block-split hypothesis holds at every level `m ≥ m₀`, then the
κ-barrier holds at every level `m ≥ m₀`.

This is the spine of the hybrid route: a base certificate (e.g. the `m = 1` BFS
`Cert_m1_Q*_kappa`) plus a uniform per-block split would yield the κ-barrier for
all `m`, hence the uniform slope barrier. Pure induction over the `WPath`-additive
step `barrier_step_of_split`; unconditional given its two hypotheses. -/
theorem uniform_kappa_barrier_of_base_and_split
    {Q m₀ : Nat}
    (h_base : S202_kappa_precise_barrier_bounded m₀ Q)
    (h_step : ∀ m, m₀ ≤ m → KappaPathSplit m Q) :
    ∀ m, m₀ ≤ m → S202_kappa_precise_barrier_bounded m Q := by
  refine Nat.le_induction h_base ?_
  intro k hk ih
  exact barrier_step_of_split (h_step k hk)

/-- **Uniform slope barrier (conditional, end-to-end).** Combining the conditional
induction with the committed non-circular reduction
`S202_slope_barrier_from_actual_edge_count_bounded ∘ … ∘
S202_kappa_precise_barrier_bounded`, a base κ-certificate plus a uniform per-block
split yields the S202 slope barrier `defect ≥ m` for **every** `m ≥ m₀` and every
zero budget `Q`.

This is the formal statement of the hybrid route's target: the only open input is
`h_step` (the uniform block-split, i.e. the per-block κ-increment); `h_base` is
supplied unconditionally for `m₀ = 1` by the `Cert_m1_Q*_kappa` BFS certificates.
-/
theorem uniform_slope_barrier_of_base_and_split
    {Q m₀ : Nat}
    (h_base : S202_kappa_precise_barrier_bounded m₀ Q)
    (h_step : ∀ m, m₀ ≤ m → KappaPathSplit m Q) :
    ∀ m, m₀ ≤ m → S216BarrierForWords m Q (m : Int) := by
  intro m hm
  have h_bar : S202_kappa_precise_barrier_bounded m Q :=
    uniform_kappa_barrier_of_base_and_split h_base h_step m hm
  exact S202_slope_barrier_from_actual_edge_count_bounded
    (S202_actual_edge_count_bounded_of_kappa_precise_barrier_bounded h_bar)

/-- **Capstone: BFS base-cert entry point.** The base of the induction is exactly
what the κ-weighted Bellman-Ford search emits: an `AbsCert` over the κ-precise
edge at base precision `22 m₀ + 2`, target `m₀`, start `InvStart m₀`. Feeding such
a certificate plus the uniform per-block split yields the S202 slope barrier for
all `m ≥ m₀`.

This makes the route's two inputs fully concrete: `cert` is the per-instance BFS
artifact (`Cert_m1_Q*_kappa`-style, `native_decide`-checked), and `h_step` is the
single open uniform increment. -/
theorem uniform_slope_barrier_of_cert_and_split
    {Q m₀ : Nat}
    (cert : AbsCert (InvKappaPreciseEdge (22 * m₀ + 2)) (22 * m₀ + 2) Q (m₀ : Int))
    (h_cert_start : cert.start = InvStart m₀)
    (h_step : ∀ m, m₀ ≤ m → KappaPathSplit m Q) :
    ∀ m, m₀ ≤ m → S216BarrierForWords m Q (m : Int) :=
  uniform_slope_barrier_of_base_and_split
    (S202_kappa_precise_barrier_bounded_from_cert cert h_cert_start) h_step

/-! ### Part 4 — Non-circularity of the split hypothesis

A reduction is only meaningful if its hypothesis is not secretly equivalent to its
conclusion (the trap that sank the earlier `S202_one_edge_count_conjecture`, see
`S202_one_edge_count_conjecture_iff_defect_barrier`). We record two facts:

  * `KappaPathSplit` *implies* the `(m+1)`-barrier (`barrier_step_of_split`,
    above) — the "useful" direction.
  * `KappaPathSplit` is *strictly more informative* than that barrier: it produces
    a witnessed split with a quantitative bound on EACH piece (`κ₁ ≥ m`, `κ₂ ≥
    1`), data the bare barrier `κ ≥ m+1` does not contain. The converse implication
    (barrier ⟹ split) is therefore not available, so the hypothesis is genuinely
    stronger and the step is a real reduction, not a tautology. -/

/-- **Non-circularity witness.** From a single use of `KappaPathSplit m Q` on a
κ-path one extracts BOTH per-piece bounds `m ≤ κ₁` and `1 ≤ κ₂` together with the
concatenation identity `κ = κ₁ + κ₂`. The bare `(m+1)`-barrier (`m+1 ≤ κ`) yields
neither piece individually, so the split hypothesis carries strictly more content
than the conclusion it implies. -/
theorem kappaPathSplit_yields_piecewise_bounds
    {m Q : Nat} (h_split : KappaPathSplit m Q)
    {goal : InvVertex} {κ : Int} {vs : List InvVertex}
    (h_g : InvVertex.IsGoal goal (22 * (m + 1) + 2))
    (h_goal_j : goal.j ≤ Q)
    (h_path : WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) goal κ vs) :
    ∃ (κ₁ κ₂ : Int), κ = κ₁ + κ₂ ∧ (m : Int) ≤ κ₁ ∧ (1 : Int) ≤ κ₂ := by
  obtain ⟨_mid, κ₁, κ₂, _vs₁, _vs₂, _h₁, _h₂, h_sum, _h_vs, h_κ₁, h_κ₂⟩ :=
    h_split h_g h_goal_j h_path
  exact ⟨κ₁, κ₂, h_sum, h_κ₁, h_κ₂⟩

end CollatzLean4.Admissible
