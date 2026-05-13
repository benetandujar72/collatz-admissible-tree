/-
**Trivial potential `Φ(v) := v.j`** — baseline of the S214 analytic
potential program.

We formalise the simplest possible potential function on the inverse
cylinder graph: `Φ(v) := v.j`. We prove:

  1. **Edge inequality** (`trivialPotential_edge_inequality`):
       for every `InvEdge R v v' ω`,  `Φ(v) ≤ ω + Φ(v')`.

  2. **Path inequality** (`trivialPotential_wpath_bound`):
       for every `WPath (InvEdge R) v t w vs`,  `Φ(v) - Φ(t) ≤ w`.

  3. **Barrier corollary** (`trivialPotential_barrier_lb`):
       any WPath from `(0, c)` to any `(j', c')` has weight `≥ -j'`.

These are weakest possible bounds (linear-in-`j` and Q-uniform), but
they constitute the **baseline** against which any non-trivial analytic
potential (combining `δ_+`, `ρ_-`, `ψ`) must improve to yield a useful
barrier `𝒞^←_{S202}(m, Q) ≥ T > 0`.

The edge inequality reduces immediately to
`InvEdge_weight_lower_bound : v.j - v'.j ≤ ω` (already proven in
`S216.lean`), since
\[
  \Phi(v) - \Phi(v') = v.j - v'.j \le \omega.
\]
-/

import CollatzLean4.S216
import CollatzLean4.PotentialBarrier
import CollatzLean4.S214Core

namespace CollatzLean4.Admissible

/-- **Trivial potential** on the inverse cylinder graph: `Φ(v) := v.j`.
This is the linear-in-`j` baseline of the S214 potential program. -/
def trivialPotential (v : InvVertex) : Int := (v.j : Int)

/-- **Edge inequality for the trivial potential**:
\[
  \Phi(v) \le \omega + \Phi(v') \quad \text{for every } \mathrm{InvEdge}(R, v, v', \omega).
\]

Reduces directly to `InvEdge_weight_lower_bound : v.j - v'.j ≤ ω`. -/
theorem trivialPotential_edge_inequality
    {R : Nat} {v v' : InvVertex} {ω : Int}
    (h : InvEdge R v v' ω) :
    trivialPotential v ≤ ω + trivialPotential v' := by
  unfold trivialPotential
  have h_lb := InvEdge_weight_lower_bound h
  linarith

/-- **Path inequality** for the trivial potential. Direct corollary of
the abstract telescoping theorem `WPath_weight_ge_potential` applied
to `Φ := trivialPotential`. -/
theorem trivialPotential_wpath_bound
    {R : Nat} {v t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) v t w vs) :
    trivialPotential v - trivialPotential t ≤ w :=
  WPath_weight_ge_potential (InvEdge R) trivialPotential
    (fun _ _ _ h => trivialPotential_edge_inequality h) h_path

/-- **Baseline barrier**: starting from `(0, c)` (i.e. `j = 0`),
every WPath to a vertex `t` has weight bounded below by `−t.j`. -/
theorem trivialPotential_barrier_lb
    {R : Nat} {start t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_start_j : start.j = 0)
    (h_path : WPath (InvEdge R) start t w vs) :
    -(t.j : Int) ≤ w := by
  have h := trivialPotential_wpath_bound h_path
  unfold trivialPotential at h
  rw [h_start_j] at h
  push_cast at h
  linarith

/-- **Q-shifted form**: the trivial potential `Ψ(v) := v.j − Q` satisfies
the same edge inequality (`Ψ(v) ≤ ω + Ψ(v')`) — the additive constant
`−Q` cancels on both sides. This is the form that appears in the S214
mixed potential template as the `−μ(Q − j)` term with `μ = 1`. -/
theorem trivialPotentialShifted_edge_inequality
    {R : Nat} {v v' : InvVertex} {ω : Int} (Q : Nat)
    (h : InvEdge R v v' ω) :
    ((v.j : Int) - (Q : Int)) ≤ ω + ((v'.j : Int) - (Q : Int)) := by
  have h_lb := InvEdge_weight_lower_bound h
  linarith

/-- **Trivial barrier certificate** as an instance of
`LocalPotentialCertificate` over the inverse cylinder graph. The
`target` value is `-Q` (so the start condition `Φ(start) ≥ target` is
satisfied trivially with equality at `start.j = 0`). Goals (vertices
with `j ≤ Q`) have `Φ ≤ 0`. -/
def trivialPotentialCertificate (R Q : Nat) (start : InvVertex)
    (h_start_j : start.j = 0) :
    LocalPotentialCertificate InvVertex where
  Φ := fun v => (v.j : Int) - (Q : Int)
  edge := InvEdge R
  start := start
  isGoal := fun v => InvVertex.IsGoal v R ∧ v.j ≤ Q
  target := -(Q : Int)
  edge_cond := fun _ _ _ h => trivialPotentialShifted_edge_inequality Q h
  goal_cond := fun v ⟨_, hjle⟩ => by
    have : (v.j : Int) ≤ (Q : Int) := by exact_mod_cast hjle
    linarith
  start_cond := by
    rw [h_start_j]
    push_cast
    linarith

/-! ### Baseline word-level barrier

The trivial potential `Φ(v) = v.j` (or its `-Q`-shift) lifts via the
`S212_forward` Word → WPath bridge to a baseline cylinder-accessibility
lower bound: every admissible word in the `m`-th S202 cylinder with
`q(u) ≤ Q` has defect `≥ -Q`. This is the **universal floor**: no
analytic potential can give a BETTER barrier without strictly
improving over the trivial-potential edge inequality somewhere on the
graph. -/

/-- **Baseline barrier for words**: every admissible word `u` in the
`m`-th S202 cylinder with `q(u) ≤ Q` has defect at least `-Q`.

This is the `T = -Q` instance of `S216BarrierForWords` — the floor of
the cylinder accessibility cost: `𝒞^←_{S202}(m, Q) ≥ -Q`. Trivially
useful only as the comparison point: any meaningful barrier requires
the analytic potential to improve over `-Q` strictly. -/
theorem trivialBaseline_for_words {m Q : Nat} :
    S216BarrierForWords m Q (-(Q : Int)) := by
  intro u h_q_bound h_cyl
  obtain ⟨vs, goal, _h_g, h_goal_j, _h_can, h_path⟩ := S212_forward m u h_cyl
  -- (evalWord u).q = Word.numZeros u.
  have h_numZeros_le : Word.numZeros u ≤ Q := by
    rw [← evalWord_q_eq]; exact h_q_bound
  have h_goal_j_le : goal.j ≤ Q := by rw [h_goal_j]; exact h_numZeros_le
  have h_mono := WPath_j_monotone h_path
  have h_vs_le : ∀ x ∈ vs, x.j ≤ Q := fun x hx => by
    have := h_mono.2 x hx
    omega
  have h_start_bound : (InvStart m).j ≤ Q := by
    show 0 ≤ Q; omega
  have h_bound := suffix_weight_bound Q h_path h_start_bound h_vs_le
  -- h_bound : -((Q : Int) - ↑(InvStart m).j) ≤ defect (evalWord u)
  have h_start_j_zero : (InvStart m).j = 0 := rfl
  rw [h_start_j_zero] at h_bound
  push_cast at h_bound
  linarith

/-! ### Parameterised potential (one-edge case)

We now lift the trivial baseline to a one-parameter family of
potentials of the form

  `Φ_λ(v) := λ · δ_+(v.c, R + v.j) + (v.j - Q)`

with `λ ≥ 0`. The `δ_+` term measures how far the cylinder of `v` is
from containing the root `1`; with positive `λ`, it adds an extra
penalty that can in principle strictly improve over the trivial
baseline `T = -Q`.

**Result of this milestone**: the edge inequality
`Φ_λ(v) ≤ ω + Φ_λ(v')` holds for **one-edges** under the uniform
scaling hypothesis `λ · (R + Q) ≤ 1`.

This decouples cleanly because along a one-edge:
  * `v'.j = v.j` (cap `r := R + v.j` is preserved);
  * `ω = τ(v'.c) ≥ 1` (from `tau_ge_one`);
  * `δ_+(c, r) ∈ [0, r]` (saturation bound).

Hence
\[
  \lambda \cdot \bigl(\delta_+(v.c, r) - \delta_+(v'.c, r)\bigr)
  \le \lambda \cdot r
  \le \lambda \cdot (R + Q)
  \le 1
  \le \tau \,=\, \omega,
\]
which is exactly the edge inequality after cancelling the `(v.j - Q)`
terms on both sides.

**Open**: the corresponding edge inequality for *zero-edges* is more
delicate (case-dependent on `τ` and on the 3-adic relation between
`v.c` and `v'.c`). A counterexample to the simple `λ ≥ 1/4`
formulation exists when `τ = 4`, `v.c ≡ 5 (mod 3^r)`, and `v'.c` is
near the root at precision `r+1`, with the cap `r` large. Closing this
case formally is the S214 analytic-potential conjecture. -/

/-- **One-edge case of the parameterised edge inequality** for the
potential `Φ_λ(v) := λ · δ_+(v.c, R+v.j) + (v.j - Q)`.

Under the scaling hypothesis `λ · (R + Q) ≤ 1` (with `λ ≥ 0` and
`v.j ≤ Q`), every inverse one-edge satisfies the abstract potential
condition `Φ_λ(v) ≤ ω + Φ_λ(v')`. -/
theorem paramPotential_oneEdge_inequality
    {R Q : Nat} (lam : Int)
    (h_lam_nn : 0 ≤ lam)
    (h_scaled : lam * ((R + Q : Nat) : Int) ≤ 1)
    {v v' : InvVertex} {ω : Int}
    (h_one : InvEdgeOne R v v' ω)
    (h_v_j_le_Q : v.j ≤ Q) :
    lam * (deltaPlus v.c (R + v.j) : Int) + ((v.j : Int) - (Q : Int)) ≤
      ω + lam * (deltaPlus v'.c (R + v'.j) : Int) + ((v'.j : Int) - (Q : Int)) := by
  obtain ⟨h_j_eq, h_X, _, h_ω⟩ := h_one
  rw [h_j_eq, h_ω]
  have h_tau := tau_ge_one h_X
  have h_dp_v_le : deltaPlus v.c (R + v.j) ≤ R + v.j := by
    unfold deltaPlus; omega
  have h_dp_v'_ge : (0 : Int) ≤ (deltaPlus v'.c (R + v.j) : Int) := by
    exact_mod_cast Nat.zero_le _
  have h_one_le_tau : (1 : Int) ≤ (tau v'.c : Int) := by exact_mod_cast h_tau
  have h_v_j_le_Q' : (v.j : Int) ≤ (Q : Int) := by exact_mod_cast h_v_j_le_Q
  have h_dp_v_le_int : (deltaPlus v.c (R + v.j) : Int) ≤ ((R + v.j : Nat) : Int) := by
    exact_mod_cast h_dp_v_le
  have h_r_le_RQ : ((R + v.j : Nat) : Int) ≤ ((R + Q : Nat) : Int) := by
    push_cast; omega
  nlinarith [mul_le_mul_of_nonneg_left h_dp_v_le_int h_lam_nn,
             mul_le_mul_of_nonneg_left h_r_le_RQ h_lam_nn,
             mul_nonneg h_lam_nn h_dp_v'_ge]

/-- **Corollary**: the strict baseline scaling `λ = 0` reduces to the
trivial potential edge inequality (already proven). -/
example {R Q : Nat} {v v' : InvVertex} {ω : Int}
    (h_one : InvEdgeOne R v v' ω) (h_v_j_le_Q : v.j ≤ Q)
    (hR : R + Q ≤ 1) :
    (1 : Int) * (deltaPlus v.c (R + v.j) : Int) + ((v.j : Int) - Q) ≤
      ω + 1 * (deltaPlus v'.c (R + v'.j) : Int) + ((v'.j : Int) - Q) := by
  apply paramPotential_oneEdge_inequality 1 (by omega) ?_ h_one h_v_j_le_Q
  push_cast; omega

/-! ### Zero-edge case: `τ ≥ 2`

For zero-edges (`v'.j = v.j + 1`, `ω = τ - 2 ≥ 0` when `τ ≥ 2`), the
edge inequality becomes
\[
  \lambda \cdot \bigl(\delta_+(v.c, r) - \delta_+(v'.c, r+1)\bigr) \le \tau - 1,
\]
which is satisfied uniformly under `λ · (R + Q) ≤ 1` since the LHS is
≤ `λ · r ≤ λ · (R + Q) ≤ 1 ≤ τ - 1` (because `τ ≥ 2`).

The case `τ = 1` (zero-edge of weight `−1`) is treated separately: it
needs the 3-adic structural fact `v'.c ≡ 2 (mod 3)`, which forces
`δ_+(v'.c, r+1) = r+1` and makes the inequality hold for *any*
`λ ≥ 0`. Closing this case formally requires unfolding the
`InvEdgeZero` consistency clause. -/

/-- **Zero-edge case of the parameterised edge inequality**, restricted
to `τ ≥ 2`. Under the same scaling `λ · (R + Q) ≤ 1`, the inequality
holds along every inverse zero-edge whose target weight satisfies
`τ(v'.c) ≥ 2`. -/
theorem paramPotential_zeroEdge_tau_ge_2_inequality
    {R Q : Nat} (lam : Int)
    (h_lam_nn : 0 ≤ lam)
    (h_scaled : lam * ((R + Q : Nat) : Int) ≤ 1)
    {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_ge_2 : 2 ≤ tau v'.c)
    (h_v_j_le_Q : v.j ≤ Q) :
    lam * (deltaPlus v.c (R + v.j) : Int) + ((v.j : Int) - (Q : Int)) ≤
      ω + lam * (deltaPlus v'.c (R + v'.j) : Int) + ((v'.j : Int) - (Q : Int)) := by
  obtain ⟨h_j_eq, _h_X, _, h_ω⟩ := h_zero
  rw [h_j_eq, h_ω]
  have h_tau_int : (2 : Int) ≤ (tau v'.c : Int) := by exact_mod_cast h_tau_ge_2
  have h_dp_v_le : deltaPlus v.c (R + v.j) ≤ R + v.j := by
    unfold deltaPlus; omega
  have h_dp_v'_ge : (0 : Int) ≤ (deltaPlus v'.c (R + (v.j + 1)) : Int) := by
    exact_mod_cast Nat.zero_le _
  have h_v_j_le_Q' : (v.j : Int) ≤ (Q : Int) := by exact_mod_cast h_v_j_le_Q
  have h_dp_v_le_int : (deltaPlus v.c (R + v.j) : Int) ≤ ((R + v.j : Nat) : Int) := by
    exact_mod_cast h_dp_v_le
  have h_r_le_RQ : ((R + v.j : Nat) : Int) ≤ ((R + Q : Nat) : Int) := by
    push_cast; omega
  have hp1 := mul_le_mul_of_nonneg_left h_dp_v_le_int h_lam_nn
  have hp2 := mul_le_mul_of_nonneg_left h_r_le_RQ h_lam_nn
  have hp3 := mul_nonneg h_lam_nn h_dp_v'_ge
  push_cast at h_dp_v_le_int h_r_le_RQ hp1 hp2 h_scaled ⊢
  linarith

/-- **Unified InvEdge case for `τ(v'.c) ≥ 2`**: combines the one-edge
and zero-edge subcases under a single scaling hypothesis. Useful for
plugging directly into the abstract `LocalPotentialCertificate.edge_cond`
when all edges incident to relevant vertices satisfy `τ ≥ 2`. -/
theorem paramPotential_edge_inequality_tau_ge_2
    {R Q : Nat} (lam : Int)
    (h_lam_nn : 0 ≤ lam)
    (h_scaled : lam * ((R + Q : Nat) : Int) ≤ 1)
    {v v' : InvVertex} {ω : Int}
    (h_edge : InvEdge R v v' ω)
    (h_v_j_le_Q : v.j ≤ Q)
    (h_tau_v' : 2 ≤ tau v'.c) :
    lam * (deltaPlus v.c (R + v.j) : Int) + ((v.j : Int) - (Q : Int)) ≤
      ω + lam * (deltaPlus v'.c (R + v'.j) : Int) + ((v'.j : Int) - (Q : Int)) := by
  rcases h_edge with h_one | h_zero
  · -- One-edge: tau ≥ 2 ≥ 1 already, but we use the weaker tau ≥ 1.
    exact paramPotential_oneEdge_inequality lam h_lam_nn h_scaled h_one h_v_j_le_Q
  · -- Zero-edge: use the tau ≥ 2 sub-case.
    exact paramPotential_zeroEdge_tau_ge_2_inequality lam h_lam_nn h_scaled
      h_zero h_tau_v' h_v_j_le_Q

/-! ### Zero-edge case: `τ = 1` (structural argument)

For zero-edges with `τ(v'.c) = 1`, the consistency clause of
`InvEdgeZero` forces `v'.c ≡ 2 (mod 3)` (taking the consistency
congruence modulo `3`). This in turn forces `ρ_+(v'.c, R + v'.j) = 0`
and hence `δ_+(v'.c, R + v'.j) = R + v'.j` (saturation at the cap),
making the edge inequality hold *for any* `λ ≥ 0` (no scaling needed). -/

/-- **Modular structural fact**: a zero-edge with `τ(v'.c) = 1` forces
`v'.c ≡ 2 (mod 3)`. Derived from the `InvEdgeZero` consistency clause
\[
  3 v.c + 1 \equiv 2 \cdot v'.c \pmod{3^{R + v'.j}},
\]
reduced modulo `3` (which is valid for `R + v'.j ≥ 1`). -/
theorem zeroEdge_tau_1_vc_mod3
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_1 : tau v'.c = 1) :
    v'.c % 3 = 2 := by
  obtain ⟨_h_j_eq, _h_X, h_consistency, _h_ω⟩ := h_zero
  rw [h_tau_1] at h_consistency
  simp only [pow_one] at h_consistency
  have h_3_dvd : (3 : Nat) ∣ 3 ^ (R + v'.j) :=
    dvd_pow_self 3 (by omega : R + v'.j ≠ 0)
  have hL := Nat.mod_mod_of_dvd (3 * v.c + 1) h_3_dvd
  have hRr := Nat.mod_mod_of_dvd (2 * v'.c) h_3_dvd
  -- hL : (3 * v.c + 1) % 3^(R+v'.j) % 3 = (3 * v.c + 1) % 3
  -- hRr: (2 * v'.c) % 3^(R+v'.j) % 3 = (2 * v'.c) % 3
  -- From h_consistency, the two LHS are equal.
  have h_mod3 : (3 * v.c + 1) % 3 = (2 * v'.c) % 3 := by
    rw [← hL, h_consistency, hRr]
  omega

/-- **Saturated target potential**: for zero-edges with `τ(v'.c) = 1`,
the root-distance potential at the target reaches its cap:
\[
  \delta_+(v'.c, R + v'.j) = R + v'.j.
\] -/
theorem zeroEdge_tau_1_deltaPlus_max
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_1 : tau v'.c = 1) :
    deltaPlus v'.c (R + v'.j) = R + v'.j := by
  have h_mod3 := zeroEdge_tau_1_vc_mod3 hR h_zero h_tau_1
  have h_vc_ne_1 : v'.c ≠ 1 := by
    intro h; rw [h] at h_mod3; omega
  -- v'.c % 3 = 2 ⇒ v'.c ≥ 2 ⇒ (v'.c - 1) % 3 = 1 ≠ 0.
  have h_vc_ge_2 : v'.c ≥ 2 := by omega
  have h_vc_sub_mod3 : (v'.c - 1) % 3 ≠ 0 := by
    have : (v'.c - 1) % 3 = 1 := by omega
    omega
  unfold deltaPlus rhoPlus
  rw [if_neg h_vc_ne_1,
      nu3_eq_zero_of_mod_three_ne_zero (v'.c - 1) (R + v'.j) h_vc_sub_mod3]
  omega

/-- **Zero-edge case of the parameterised edge inequality**, sub-case
`τ = 1`. The structural saturation `δ_+(v'.c, R + v'.j) = R + v'.j`
makes the inequality hold for **any** `λ ≥ 0` — no scaling hypothesis
on `λ · (R + Q)` is needed in this case. -/
theorem paramPotential_zeroEdge_tau_1_inequality
    {R Q : Nat} (lam : Int)
    (h_lam_nn : 0 ≤ lam)
    (hR : 1 ≤ R)
    {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_1 : tau v'.c = 1) :
    lam * (deltaPlus v.c (R + v.j) : Int) + ((v.j : Int) - (Q : Int)) ≤
      ω + lam * (deltaPlus v'.c (R + v'.j) : Int) + ((v'.j : Int) - (Q : Int)) := by
  -- Extract structural lemmas BEFORE destructuring h_zero.
  have h_dp_v'_max := zeroEdge_tau_1_deltaPlus_max hR h_zero h_tau_1
  obtain ⟨h_j_eq, _h_X, _, h_ω⟩ := h_zero
  have h_dp_v_le : deltaPlus v.c (R + v.j) ≤ R + v.j := by
    unfold deltaPlus; omega
  rw [h_ω, h_tau_1, h_dp_v'_max, h_j_eq]
  -- ω now: ((1 : Nat) : Int) - 2 = -1.
  -- δ_+(v'.c, R + v'.j) replaced by R + v'.j (with v'.j = v.j + 1).
  -- Goal: lam * δ_+(v.c, R+v.j) + (v.j - Q) ≤
  --        ((1:Nat):Int) - 2 + lam * (R + (v.j+1)) + ((v.j+1) - Q).
  have h_dp_v_le_int : (deltaPlus v.c (R + v.j) : Int) ≤ ((R + v.j : Nat) : Int) := by
    exact_mod_cast h_dp_v_le
  have hp1 := mul_le_mul_of_nonneg_left h_dp_v_le_int h_lam_nn
  push_cast at hp1 ⊢
  linarith

/-- **Complete edge inequality for zero-edges** (no `τ` restriction):
combines the `τ ≥ 2` and `τ = 1` sub-cases via `tau_ge_one`. -/
theorem paramPotential_zeroEdge_inequality
    {R Q : Nat} (lam : Int)
    (h_lam_nn : 0 ≤ lam)
    (h_scaled : lam * ((R + Q : Nat) : Int) ≤ 1)
    (hR : 1 ≤ R)
    {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_v_j_le_Q : v.j ≤ Q) :
    lam * (deltaPlus v.c (R + v.j) : Int) + ((v.j : Int) - (Q : Int)) ≤
      ω + lam * (deltaPlus v'.c (R + v'.j) : Int) + ((v'.j : Int) - (Q : Int)) := by
  -- Project to InX without destructuring h_zero.
  have h_X : InX v'.c := h_zero.2.1
  have h_tau_ge_1 := tau_ge_one h_X
  by_cases h_tau_1 : tau v'.c = 1
  · exact paramPotential_zeroEdge_tau_1_inequality lam h_lam_nn hR h_zero h_tau_1
  · have h_tau_ge_2 : 2 ≤ tau v'.c := by omega
    exact paramPotential_zeroEdge_tau_ge_2_inequality lam h_lam_nn h_scaled
      h_zero h_tau_ge_2 h_v_j_le_Q

/-- **Edge inequality for the parameterised potential on ALL edges**.

For every `R, Q, lam` with `0 ≤ lam` and `lam · (R + Q) ≤ 1` and
`R ≥ 1`, the potential
\[
  \Phi_\lambda(v) := \lambda \cdot \delta_+(v.c, R + v.j) + (v.j - Q)
\]
satisfies the abstract edge inequality
`Φ_λ(v) ≤ ω + Φ_λ(v')` along every `InvEdge R v v' ω` with `v.j ≤ Q`.

This **completes the edge condition** for `LocalPotentialCertificate`
on the inverse cylinder graph, parameterised by `lam`. -/
theorem paramPotential_edge_inequality
    {R Q : Nat} (lam : Int)
    (h_lam_nn : 0 ≤ lam)
    (h_scaled : lam * ((R + Q : Nat) : Int) ≤ 1)
    (hR : 1 ≤ R)
    {v v' : InvVertex} {ω : Int}
    (h_edge : InvEdge R v v' ω)
    (h_v_j_le_Q : v.j ≤ Q) :
    lam * (deltaPlus v.c (R + v.j) : Int) + ((v.j : Int) - (Q : Int)) ≤
      ω + lam * (deltaPlus v'.c (R + v'.j) : Int) + ((v'.j : Int) - (Q : Int)) := by
  rcases h_edge with h_one | h_zero
  · exact paramPotential_oneEdge_inequality lam h_lam_nn h_scaled h_one h_v_j_le_Q
  · exact paramPotential_zeroEdge_inequality lam h_lam_nn h_scaled hR h_zero h_v_j_le_Q

end CollatzLean4.Admissible
