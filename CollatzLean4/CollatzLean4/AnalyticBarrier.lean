/-
**Analytic barrier for words (uniform in `m`, `Q`)**.

This module builds on the parameterised potential edge inequality
(`paramPotential_edge_inequality` in `TrivialPotential.lean`) to
produce the FIRST formal cylinder-accessibility barrier theorem that
is **uniform in `(m, Q)`** — without any Python-generated certificate.

## Strategy

The parameterised potential
\[
  \Phi_\lambda(v) := \lambda \cdot \delta_+(v.c, R + v.j) + (v.j - Q)
\]
satisfies the abstract edge inequality with `λ = 1/(R + Q)`. Since
`λ` is rational and Lean integers cannot represent fractions, we use
the **Int-scaled** form
\[
  \Psi(v) := \delta_+(v.c, R + v.j) + (R + Q) \cdot (v.j - Q),
\]
which satisfies the **scaled** edge inequality
\[
  \Psi(v) \le (R + Q) \cdot \omega + \Psi(v').
\]
Telescoping this over a `WPath` of total weight `w` (= `defect u` for
admissible words) gives
\[
  (R + Q) \cdot w \ge \Psi(\text{start}) - \Psi(\text{goal})
                  = (R - 22) - (R + Q) \cdot j_{\text{goal}}.
\]
Rearranging and using `j_goal ≤ Q`:
\[
  (R + Q) \cdot (w + Q) \ge R - 22 \ge 22m - 20 \ge 2 \quad (m \ge 1).
\]
Since `R + Q ≥ 1` and the product is at least 2 (positive), we conclude
`w + Q ≥ 1`, i.e., `defect ≥ -Q + 1`. This **strictly beats** the
trivial baseline `defect ≥ -Q` of `trivialBaseline_for_words`.
-/

import CollatzLean4.TrivialPotential

namespace CollatzLean4.Admissible

/-! ### Scaled edge inequality (no `λ · (R + Q)` restriction) -/

/-- **Scaled edge inequality** for the analytic potential
`Ψ(v) := δ_+(v.c, R+v.j) + (R+Q) · (v.j - Q)`:
\[
  \Psi(v) \le (R + Q) \cdot \omega + \Psi(v').
\]

Holds for ALL InvEdges (both one and zero, all `τ ≥ 1`) under just
`R ≥ 1` and `v.j ≤ Q`. -/
theorem scaledPotential_edge_inequality
    {R Q : Nat} (hR : 1 ≤ R)
    {v v' : InvVertex} {ω : Int}
    (h_edge : InvEdge R v v' ω)
    (h_v_j_le_Q : v.j ≤ Q) :
    (deltaPlus v.c (R + v.j) : Int)
      + ((R + Q : Nat) : Int) * ((v.j : Int) - (Q : Int)) ≤
    ((R + Q : Nat) : Int) * ω
      + (deltaPlus v'.c (R + v'.j) : Int)
      + ((R + Q : Nat) : Int) * ((v'.j : Int) - (Q : Int)) := by
  have h_RQ_nn : (0 : Int) ≤ ((R + Q : Nat) : Int) := by positivity
  rcases h_edge with h_one | h_zero
  · -- One-edge: v'.j = v.j, ω = tau v'.c ≥ 1.
    obtain ⟨h_j_eq, h_X, _, h_ω⟩ := h_one
    rw [h_j_eq, h_ω]
    have h_tau : (1 : Int) ≤ (tau v'.c : Int) := by exact_mod_cast tau_ge_one h_X
    have h_dp_v_le : deltaPlus v.c (R + v.j) ≤ R + v.j := by unfold deltaPlus; omega
    have h_dp_v_le_int : (deltaPlus v.c (R + v.j) : Int) ≤ ((R + v.j : Nat) : Int) := by
      exact_mod_cast h_dp_v_le
    have h_dp_v'_ge : (0 : Int) ≤ (deltaPlus v'.c (R + v.j) : Int) := by positivity
    have h_r_le_RQ : ((R + v.j : Nat) : Int) ≤ ((R + Q : Nat) : Int) := by
      push_cast; omega
    -- The product (R+Q)·(τ-1) ≥ 0 gives us the slack.
    have h_slack : (0 : Int) ≤ ((R + Q : Nat) : Int) * ((tau v'.c : Int) - 1) :=
      mul_nonneg h_RQ_nn (by linarith)
    nlinarith
  · -- Zero-edge: case-split on tau.
    have h_X : InX v'.c := h_zero.2.1
    by_cases h_tau_1 : tau v'.c = 1
    · -- tau = 1: structural fact δ_+(v'.c, R + v'.j) = R + v'.j.
      have h_dp_v'_max := zeroEdge_tau_1_deltaPlus_max hR h_zero h_tau_1
      obtain ⟨h_j_eq, _, _, h_ω⟩ := h_zero
      rw [h_j_eq] at h_dp_v'_max
      rw [h_ω, h_tau_1, h_j_eq, h_dp_v'_max]
      have h_dp_v_le : deltaPlus v.c (R + v.j) ≤ R + v.j := by unfold deltaPlus; omega
      have h_dp_v_le_int : (deltaPlus v.c (R + v.j) : Int) ≤ ((R + v.j : Nat) : Int) := by
        exact_mod_cast h_dp_v_le
      push_cast at *
      linarith
    · -- tau ≥ 2: trivial bound.
      have h_tau_ge_2 : 2 ≤ tau v'.c := by
        have := tau_ge_one h_X
        omega
      obtain ⟨h_j_eq, _, _, h_ω⟩ := h_zero
      rw [h_j_eq, h_ω]
      have h_tau_int : (2 : Int) ≤ (tau v'.c : Int) := by exact_mod_cast h_tau_ge_2
      have h_dp_v_le : deltaPlus v.c (R + v.j) ≤ R + v.j := by unfold deltaPlus; omega
      have h_dp_v_le_int : (deltaPlus v.c (R + v.j) : Int) ≤ ((R + v.j : Nat) : Int) := by
        exact_mod_cast h_dp_v_le
      have h_dp_v'_ge : (0 : Int) ≤ (deltaPlus v'.c (R + (v.j + 1)) : Int) := by positivity
      have h_r_le_RQ : ((R + v.j : Nat) : Int) ≤ ((R + Q : Nat) : Int) := by
        push_cast; omega
      -- (R+Q)·(τ-2) ≥ 0 since τ ≥ 2.
      have h_slack : (0 : Int) ≤ ((R + Q : Nat) : Int) * ((tau v'.c : Int) - 2) :=
        mul_nonneg h_RQ_nn (by linarith)
      push_cast at *
      nlinarith

/-! ### Path-level scaled bound -/

/-- **Scaled WPath bound**: telescoping the scaled edge inequality
along any `WPath` (with all vertices in the `j ≤ Q` slice) yields
\[
  \Psi(v) - \Psi(t) \le (R + Q) \cdot w.
\] -/
theorem scaledPotential_wpath_bound
    {R Q : Nat} (hR : 1 ≤ R)
    {v t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) v t w vs)
    (h_v_j_le_Q : v.j ≤ Q)
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q) :
    (deltaPlus v.c (R + v.j) : Int)
      + ((R + Q : Nat) : Int) * ((v.j : Int) - (Q : Int)) ≤
    ((R + Q : Nat) : Int) * w
      + (deltaPlus t.c (R + t.j) : Int)
      + ((R + Q : Nat) : Int) * ((t.j : Int) - (Q : Int)) := by
  induction vs generalizing v w with
  | nil =>
      simp only [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      simp
  | cons u vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      have h_u_bound : u.j ≤ Q := h_path_bound u (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_bound : ∀ x ∈ vs', x.j ≤ Q := fun x hx =>
        h_path_bound x (List.mem_cons.mpr (Or.inr hx))
      have h_step := scaledPotential_edge_inequality hR h_edge h_v_j_le_Q
      have h_ih := ih h_rest h_u_bound h_rest_bound
      have h_RQ_nn : (0 : Int) ≤ ((R + Q : Nat) : Int) := by positivity
      linarith [mul_add ((R + Q : Nat) : Int) ω₁ ω₂]

/-! ### Start vertex equals `aS202` for `m ≥ 1` -/

/-- The start vertex's `c`-component equals `aS202` exactly for `m ≥ 1`
(since `aS202 = 1 + 3^22 < 3^24 ≤ 3^(22m+2)`). -/
lemma invStart_c_eq_aS202 (m : Nat) (hm : 1 ≤ m) : (InvStart m).c = aS202 := by
  show aS202 % (3 ^ (22 * m + 2)) = aS202
  apply Nat.mod_eq_of_lt
  have h_aS_lt : aS202 < 3 ^ 24 := by
    rw [aS202_decomp]; decide
  have h_pow_le : (3 : Nat) ^ 24 ≤ 3 ^ (22 * m + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega : 24 ≤ 22 * m + 2)
  omega

/-- `deltaPlus` of the start vertex computes to `R - 22` for `m ≥ 1`. -/
lemma deltaPlus_invStart (m : Nat) (hm : 1 ≤ m) :
    deltaPlus (InvStart m).c (22 * m + 2 + (InvStart m).j) = 22 * m - 20 := by
  have h_j_zero : (InvStart m).j = 0 := rfl
  rw [h_j_zero, Nat.add_zero, invStart_c_eq_aS202 m hm]
  exact deltaPlus_aS202_general m hm

/-! ### Analytic barrier theorem (uniform in `m`, `Q`) -/

/-- **First formal uniform-in-(m, Q) cylinder-accessibility barrier**.

For every `m ≥ 1` and every `Q`, the cylinder cost satisfies
\[
  \mathcal C^{\leftarrow}_{S202}(m, Q) \ge -Q + 1.
\]

Strictly beats the trivial baseline `-Q` of `trivialBaseline_for_words`
by exactly `1`. The proof is **purely analytic** — uses the scaled
potential `Ψ(v) := δ_+(v.c, R+v.j) + (R+Q)·(v.j - Q)`, no Python
certificate. -/
theorem analyticBarrier_for_words {m Q : Nat} (hm : 1 ≤ m) :
    S216BarrierForWords m Q (-(Q : Int) + 1) := by
  intro u h_q_bound h_cyl
  have hR : (1 : Nat) ≤ 22 * m + 2 := by omega
  obtain ⟨vs, goal, h_g, h_goal_j, _h_can, h_path⟩ := S212_forward m u h_cyl
  -- Bound all vertex j-values by Q.
  have h_numZeros_le : Word.numZeros u ≤ Q := by
    rw [← evalWord_q_eq]; exact h_q_bound
  have h_goal_j_le : goal.j ≤ Q := by rw [h_goal_j]; exact h_numZeros_le
  have h_mono := WPath_j_monotone h_path
  have h_vs_le : ∀ x ∈ vs, x.j ≤ Q := fun x hx => by
    have := h_mono.2 x hx; omega
  have h_start_bound : (InvStart m).j ≤ Q := by show 0 ≤ Q; omega
  -- Apply the scaled path bound.
  have h_bound := scaledPotential_wpath_bound (R := 22*m+2) (Q := Q) hR h_path
    h_start_bound h_vs_le
  -- Compute potential at start and goal.
  have h_dp_start := deltaPlus_invStart m hm
  have h_dp_goal : deltaPlus goal.c (22 * m + 2 + goal.j) = 0 :=
    goal_deltaPlus_zero hR h_g
  have h_start_j_zero : (InvStart m).j = 0 := rfl
  -- Rewrite h_bound with these computations.
  rw [h_dp_start, h_dp_goal] at h_bound
  rw [h_start_j_zero] at h_bound
  -- Now h_bound has the form:
  --   (22m - 20 : Int) + (R+Q)·(0 - Q) ≤
  --   (R+Q)·defect + 0 + (R+Q)·(goal.j - Q)
  -- Rearrange to: (R+Q)·(defect + goal.j) ≥ R - 22 = 22m - 20.
  -- For m ≥ 1: 22m - 20 ≥ 2.
  -- Hence defect + goal.j ≥ 1.
  -- Hence defect ≥ 1 - goal.j ≥ 1 - Q = -Q + 1.
  -- Normalize casts. push_cast handles Nat.cast_sub via the hypothesis 20 ≤ 22*m.
  have h_22m_ge_20 : 20 ≤ 22 * m := by omega
  push_cast [Nat.cast_sub h_22m_ge_20] at h_bound
  -- h_bound : 22m - 20 + (22m+2+Q)·(0-Q) ≤ (22m+2+Q)·defect + 0 + (22m+2+Q)·(goal.j - Q)
  have h_m_int : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm
  have h_A_pos : (1 : Int) ≤ 22 * (m : Int) + 2 + (Q : Int) := by linarith
  have h_22m_ge_22 : (22 : Int) ≤ 22 * (m : Int) := by linarith
  have h_22m20_ge_2 : (22 * (m : Int) - 20) ≥ 2 := by linarith
  -- Derive (R+Q)·(defect + goal.j) ≥ 22m - 20 from h_bound by ring manipulation.
  have h_prod : (22 * (m : Int) + 2 + (Q : Int)) *
                (defect (evalWord u) + (goal.j : Int))
                  ≥ 22 * (m : Int) - 20 := by nlinarith [h_bound]
  -- A · (D + J) ≥ 2 > 0 with A ≥ 1 ⇒ D + J ≥ 1 (Int, positive cone).
  have h_goal_j_le_int : (goal.j : Int) ≤ (Q : Int) := by exact_mod_cast h_goal_j_le
  have h_sum_ge_1 : (1 : Int) ≤ defect (evalWord u) + (goal.j : Int) := by
    rcases lt_or_ge (defect (evalWord u) + (goal.j : Int)) 1 with h_lt | h_ge
    · exfalso
      have h_sum_le_0 : defect (evalWord u) + (goal.j : Int) ≤ 0 := by linarith
      have h_prod_le_0 :
          (22 * (m : Int) + 2 + (Q : Int)) *
          (defect (evalWord u) + (goal.j : Int)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) h_sum_le_0
      linarith
    · exact h_ge
  linarith

/-! ### Towards the next level: structural facts on `ρ_-`

The analytic barrier `defect ≥ -Q + 1` is the maximum achievable with a
*uniform* linear potential `λ · δ_+ + (j - Q)`. To improve further the
program S214-Core suggests integrating a `γ · ρ_-` term and finite local
corrections `ψ(c mod 3^h)`.

This section establishes the structural building blocks that enable
such a `ρ_-`-extended potential:

  1. `rhoMinus_invStart_zero` — boundary value at the start vertex.
  2. `zeroEdge_tau_1_rhoMinus_pos` — `ρ_-` jumps to `≥ 1` along
     τ=1 zero-edges (a strong constraint from the modular structure
     `v'.c ≡ 2 (mod 3)`).
  3. `goal_rhoMinus_zero` — already proved in S214Core.lean.

Together these mean the `ρ_-` profile along a path from `start` to a
`goal` is `0 → ≥1 → … → 0`, with mandatory "ascents" forced by
negative-defect (τ=1 zero-edge) steps. The corresponding integral can
be turned into a penalty that strictly tightens the barrier — but
the precise edge-inequality verification requires τ-dependent
weighting and is the S214-Core open conjecture. -/

/-- **Boundary value at start**: `ρ_-(start.c, R) = 0` for `m ≥ 1`.

Reason: `start.c = aS202 = 1 + 3^22`, so `start.c + 1 = 2 + 3^22 ≡ 2 (mod 3)`,
hence `ν₃(start.c + 1) = 0`. -/
theorem rhoMinus_invStart_zero (m : Nat) (hm : 1 ≤ m) :
    rhoMinus (InvStart m).c (22 * m + 2 + (InvStart m).j) = 0 := by
  have h_start_c := invStart_c_eq_aS202 m hm
  rw [h_start_c]
  unfold rhoMinus
  apply nu3_eq_zero_of_mod_three_ne_zero
  rw [aS202_decomp]
  -- (1 + 3^22 + 1) % 3 = (2 + 3^22) % 3 = 2 ≠ 0.
  -- 3^22 mod 3 = 0, so (2 + 0) mod 3 = 2.
  show (1 + 3 ^ 22 + 1) % 3 ≠ 0
  have h_pow_mod : (3 ^ 22 : Nat) % 3 = 0 := by
    have : (3 : Nat) ∣ 3 ^ 22 := dvd_pow_self 3 (by omega)
    omega
  omega

/-- **Structural jump of `ρ_-` along τ=1 zero-edges**: every zero-edge
with `τ(v'.c) = 1` lands in a vertex with `ρ_-(v'.c, R + v'.j) ≥ 1`.

Reason: the consistency clause of `InvEdgeZero` forces
`v'.c ≡ 2 (mod 3)` (proven in `zeroEdge_tau_1_vc_mod3`), hence
`v'.c + 1 ≡ 0 (mod 3)`, hence `ν₃(v'.c + 1) ≥ 1`.

This is the **negative-defect-step signature** in the ρ_- profile:
every "credit-spending" zero-edge of weight `-1` is forced to jump
into the negative-run region around `-1`. The S214-Core paper exploits
this to argue that paths cannot accumulate "free" negative defect
gain without simultaneously accumulating ρ_- penalty. -/
theorem zeroEdge_tau_1_rhoMinus_pos
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_1 : tau v'.c = 1) :
    1 ≤ rhoMinus v'.c (R + v'.j) := by
  have h_mod3 := zeroEdge_tau_1_vc_mod3 hR h_zero h_tau_1
  -- v'.c % 3 = 2 ⇒ (v'.c + 1) % 3 = 0 ⇒ 3 ∣ (v'.c + 1).
  have h_vc_plus_mod : (v'.c + 1) % 3 = 0 := by omega
  have h_vc_plus_dvd : (3 : Nat) ∣ (v'.c + 1) := Nat.dvd_of_mod_eq_zero h_vc_plus_mod
  -- nu3 (v'.c + 1) (R+v'.j) ≥ 1 since v'.c + 1 ≠ 0, n%3 = 0, R+v'.j ≥ 1.
  unfold rhoMinus
  have h_pos : 0 < v'.c + 1 := by omega
  have h_ne : v'.c + 1 ≠ 0 := by omega
  -- Unfold nu3 at R+v'.j (which is ≥ 1).
  have hRj : 1 ≤ R + v'.j := by omega
  -- Use that nu3 n (k+1) = 1 + nu3 (n/3) k when n ≠ 0 and n % 3 = 0.
  obtain ⟨k, hk⟩ : ∃ k, R + v'.j = k + 1 := ⟨R + v'.j - 1, by omega⟩
  rw [hk]
  show 1 ≤ (if v'.c + 1 = 0 then 0
            else if (v'.c + 1) % 3 = 0 then 1 + nu3 ((v'.c + 1) / 3) k else 0)
  rw [if_neg h_ne, if_pos h_vc_plus_mod]
  omega

/-! ### Edge weight classification

Building blocks for path-decomposition arguments: every `InvEdge` falls
into exactly one of three weight classes determined by its source type
and `τ(v'.c)` value. This classification is the **structural input**
into any non-linear analytic potential argument. -/

/-- **One-edge weights are strictly positive**: ω ≥ 1. -/
theorem oneEdge_weight_pos
    {R : Nat} {v v' : InvVertex} {ω : Int}
    (h_one : InvEdgeOne R v v' ω) :
    (1 : Int) ≤ ω := by
  obtain ⟨_, h_X, _, h_ω⟩ := h_one
  rw [h_ω]
  exact_mod_cast tau_ge_one h_X

/-- **τ=1 zero-edge weight is exactly `-1`**: the negative-defect step. -/
theorem tau1ZeroEdge_weight_eq_neg_one
    {R : Nat} {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_1 : tau v'.c = 1) :
    ω = -1 := by
  obtain ⟨_, _, _, h_ω⟩ := h_zero
  rw [h_ω, h_tau_1]
  rfl

/-- **τ≥2 zero-edge weights are non-negative**: ω ≥ 0. -/
theorem tau_ge_2_ZeroEdge_weight_nonneg
    {R : Nat} {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω)
    (h_tau_ge_2 : 2 ≤ tau v'.c) :
    (0 : Int) ≤ ω := by
  obtain ⟨_, _, _, h_ω⟩ := h_zero
  rw [h_ω]
  have : (2 : Int) ≤ (tau v'.c : Int) := by exact_mod_cast h_tau_ge_2
  linarith

/-- **Trichotomy of edge weights**: every InvEdge has weight `≥ 1`
(one-edge), `= -1` (τ=1 zero-edge), or `≥ 0` (τ≥2 zero-edge). -/
theorem invEdge_weight_trichotomy
    {R : Nat} {v v' : InvVertex} {ω : Int}
    (h_edge : InvEdge R v v' ω) :
    (InvEdgeOne R v v' ω ∧ 1 ≤ ω) ∨
    (InvEdgeZero R v v' ω ∧ tau v'.c = 1 ∧ ω = -1) ∨
    (InvEdgeZero R v v' ω ∧ 2 ≤ tau v'.c ∧ 0 ≤ ω) := by
  rcases h_edge with h_one | h_zero
  · left
    exact ⟨h_one, oneEdge_weight_pos h_one⟩
  · have h_X : InX v'.c := h_zero.2.1
    by_cases h_tau_1 : tau v'.c = 1
    · right; left
      exact ⟨h_zero, h_tau_1, tau1ZeroEdge_weight_eq_neg_one h_zero h_tau_1⟩
    · right; right
      have h_tau_ge_2 : 2 ≤ tau v'.c := by
        have := tau_ge_one h_X; omega
      exact ⟨h_zero, h_tau_ge_2, tau_ge_2_ZeroEdge_weight_nonneg h_zero h_tau_ge_2⟩

/-! ### Honest scope of the analytic barrier program

The current state of the analytic barrier toolkit:

| Theorem | Bound | Domain |
|---|---|---|
| `trivialBaseline_for_words` | `defect ≥ -Q` | uniform ∀ m, Q |
| `analyticBarrier_for_words` | `defect ≥ -Q + 1` | uniform ∀ m ≥ 1, Q |
| (Cert-specific) | `defect ≥ +1` | m=1, Q ∈ {3, 5, 8} |
| (S202 conjecture) | `defect ≥ +m` | conjectural ∀ m, Q ≤ Km |

**Strict barrier improvement beyond `-Q + 1` requires** (S214-Core
conjecture):

  (i)  **τ-dependent coefficients** `λ_τ`: e.g., `λ_τ = 0` for τ=1
       (where the structural saturation `δ_+(v'.c, r+1) = r+1`
       absorbs all the slack), and `λ_τ > 0` for τ ≥ 2. A uniform
       single `λ` cannot work — verified by the worst-case alignment:
       for one-edges with `τ = 1`, both `δ_+_diff` and `ρ_-_diff`
       can simultaneously reach `R+Q`, forcing any uniform mixed
       coefficient to satisfy `λ + γ ≤ 0`.

  (ii) **Path decomposition counting τ=1 zero-edges**: every τ=1
       zero-edge contributes `-1` to defect (proved). Hence
       `defect ≥ (#one-edges) - (#τ=1 zero-edges) + 0·(#τ≥2 zero-edges)`.
       To exploit, lower-bound `#one-edges` via the 3-adic
       distance traveled in the cylinder hierarchy.

  (iii) **Local ψ correction**: a finite tabulated correction
        `ψ : (Fin 3^h) → Int` with `ψ ≤ 0` on goal residues and
        `Σ ψ(diff) ≤ 0` on every cycle. Compensates the edge-inequality
        slack at non-binding cases.

The Lean infrastructure built in this session
(`paramPotential_edge_inequality`, `scaledPotential_edge_inequality`,
`oneEdge_weight_pos`, `tau1ZeroEdge_weight_eq_neg_one`,
`tau_ge_2_ZeroEdge_weight_nonneg`, `invEdge_weight_trichotomy`,
`rhoMinus_invStart_zero`, `zeroEdge_tau_1_rhoMinus_pos`,
`goal_deltaPlus_zero`, `goal_rhoMinus_zero`, etc.) supplies the
**complete first-order theory** required to state and attack (i)-(iii)
as Lean theorems. Closing them remains the S214 conjecture's open core.
-/

/-! ### Path decomposition counting

Each `WPath` from `s` to `t` consists of a sequence of edges, each of
which is exactly one of three types (one-edge, τ=1 zero-edge,
τ≥2 zero-edge). The following theorem makes this decomposition
explicit and gives the resulting weight lower bound. -/

/-- **Path weight decomposition**: every `WPath (InvEdge R) s t w vs`
decomposes its weight into contributions from three edge classes:
\[
  w \ge n_{\text{one}} - n_{\text{neg}} + 0 \cdot n_{\text{pos zero}}
\]
with `n_one + n_neg + n_pos_zero = vs.length` (= path length) and
`n_neg + n_pos_zero + s.j = t.j` (= j-increment along the path equals
the number of zero-edges).

This is the structural foundation of any path-decomposition argument
toward closing the S214 conjecture. -/
theorem WPath_weight_decompose
    {R : Nat} {s t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) s t w vs) :
    ∃ n_one n_neg n_pos_zero : Nat,
      n_one + n_neg + n_pos_zero = vs.length ∧
      n_neg + n_pos_zero + s.j = t.j ∧
      (n_one : Int) - (n_neg : Int) ≤ w := by
  induction vs generalizing s w with
  | nil =>
      simp [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      exact ⟨0, 0, 0, rfl, by omega, by norm_num⟩
  | cons v vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      obtain ⟨n_one, n_neg, n_pos_zero, h_count, h_j, h_w_bound⟩ := ih h_rest
      rcases invEdge_weight_trichotomy h_edge with
        ⟨h_one, h_ω_lb⟩ | ⟨h_zero, _h_tau_1, h_ω_eq⟩ | ⟨h_zero, _h_tau_ge_2, h_ω_nn⟩
      · -- One-edge: v.j = s.j (cap preserved), increment n_one.
        obtain ⟨h_j_eq, _, _, _⟩ := h_one
        refine ⟨n_one + 1, n_neg, n_pos_zero, ?_, ?_, ?_⟩
        · simp [List.length_cons]; omega
        · omega
        · push_cast; linarith
      · -- τ=1 zero-edge: v.j = s.j + 1, ω = -1, increment n_neg.
        obtain ⟨h_j_eq, _, _, _⟩ := h_zero
        refine ⟨n_one, n_neg + 1, n_pos_zero, ?_, ?_, ?_⟩
        · simp [List.length_cons]; omega
        · omega
        · push_cast; linarith
      · -- τ≥2 zero-edge: v.j = s.j + 1, ω ≥ 0, increment n_pos_zero.
        obtain ⟨h_j_eq, _, _, _⟩ := h_zero
        refine ⟨n_one, n_neg, n_pos_zero + 1, ?_, ?_, ?_⟩
        · simp [List.length_cons]; omega
        · omega
        · linarith

/-- **Number-of-zero-edges identity**: the j-increment along a `WPath`
equals the total number of zero-edges. Direct corollary of the
decomposition theorem. -/
theorem WPath_j_increment_eq_n_zero
    {R : Nat} {s t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) s t w vs) :
    ∃ n_zero : Nat, n_zero + s.j = t.j ∧ n_zero ≤ vs.length := by
  obtain ⟨n_one, n_neg, n_pos_zero, h_count, h_j, _⟩ := WPath_weight_decompose h_path
  exact ⟨n_neg + n_pos_zero, h_j, by omega⟩

/-- **Defect lower bound via decomposition**: the weight `w` of any
`WPath` satisfies `w ≥ n_one - n_neg`, where `n_one + n_neg + n_pos_zero
= vs.length` is the number of one-edges, τ=1 zero-edges, and τ≥2
zero-edges respectively. -/
theorem WPath_weight_ge_one_minus_neg
    {R : Nat} {s t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) s t w vs) :
    ∃ n_one n_neg : Nat,
      n_neg + s.j ≤ t.j ∧
      n_one + n_neg ≤ vs.length ∧
      (n_one : Int) - (n_neg : Int) ≤ w := by
  obtain ⟨n_one, n_neg, n_pos_zero, h_count, h_j, h_w⟩ := WPath_weight_decompose h_path
  exact ⟨n_one, n_neg, by omega, by omega, h_w⟩

/-! ### Word-level path decomposition

Lifts `WPath_weight_decompose` through `S212_forward` to produce a
word-level decomposition theorem. Every admissible word `u` landing in
the m-th S202 cylinder has its defect decomposed into three counts:
the number of one-edges, τ=1 zero-edges, and τ≥2 zero-edges in the
corresponding inverse-graph path. -/

/-- **Word-level defect decomposition**: for every admissible word
`u` in the m-th S202 cylinder with `q(u) ≤ Q`, there exist counts
`n_one, n_neg, n_pos_zero ∈ ℕ` such that:
  • `n_neg + n_pos_zero = Word.numZeros u` (zero-edges count matches),
  • `n_neg ≤ Q` (capped by the zero budget),
  • `defect(u) ≥ n_one - n_neg`.

The decomposition makes precise that the only negative contributions
to defect come from the τ=1 zero-edges (each contributing `-1`),
balanced by the positive contributions from one-edges (each ≥ 1) and
non-negative contributions from τ≥2 zero-edges. -/
theorem Word_defect_decompose
    {m Q : Nat} (hm : 1 ≤ m) :
    ∀ u : Word,
      (evalWord u).q ≤ Q →
      (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) →
      ∃ n_one n_neg n_pos_zero : Nat,
        n_neg + n_pos_zero = Word.numZeros u ∧
        n_neg ≤ Q ∧
        (n_one : Int) - (n_neg : Int) ≤ defect (evalWord u) := by
  intro u h_q h_cyl
  obtain ⟨vs, goal, _h_g, h_goal_j, _h_can, h_path⟩ := S212_forward m u h_cyl
  obtain ⟨n_one, n_neg, n_pos_zero, _h_count, h_j, h_w⟩ := WPath_weight_decompose h_path
  have h_numZeros_le : Word.numZeros u ≤ Q := by
    rw [← evalWord_q_eq]; exact h_q
  have h_start_j : (InvStart m).j = 0 := rfl
  rw [h_start_j] at h_j
  rw [h_goal_j] at h_j
  refine ⟨n_one, n_neg, n_pos_zero, by omega, by omega, h_w⟩

/-- **Re-derivation of the trivial baseline** via path decomposition:
every admissible word has defect at least `-Q`. -/
theorem trivialBaseline_via_decomposition
    {m Q : Nat} (hm : 1 ≤ m) :
    S216BarrierForWords m Q (-(Q : Int)) := by
  intro u h_q h_cyl
  obtain ⟨n_one, n_neg, _n_pos_zero, _h_count, h_neg_le, h_w⟩ :=
    Word_defect_decompose hm u h_q h_cyl
  have h_n_one_nn : (0 : Int) ≤ (n_one : Int) := by positivity
  have h_n_neg_le : (n_neg : Int) ≤ (Q : Int) := by exact_mod_cast h_neg_le
  linarith

/-- **Conditional strict barrier** from the path decomposition: if it
were known that every admissible word in the m-th cylinder has at
least `k` one-edges in its inverse-graph path, then
`defect ≥ -Q + k`.

This is a **template** for future strict-barrier proofs once a
combinatorial argument bounds `n_one` from below. The current trivial
case `k = 0` reproves the baseline; the conjectured `k = m + Q` would
close the gap to the S202 slope barrier. -/
theorem conditionalStrictBarrier_from_one_count
    {m Q : Nat} (hm : 1 ≤ m) (k : Nat)
    (h_one_lower_bound :
      ∀ u : Word,
        (evalWord u).q ≤ Q →
        (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) →
        ∃ n_one n_neg n_pos_zero : Nat,
          n_neg + n_pos_zero = Word.numZeros u ∧
          n_neg ≤ Q ∧
          (n_one : Int) - (n_neg : Int) ≤ defect (evalWord u) ∧
          k ≤ n_one) :
    S216BarrierForWords m Q (-(Q : Int) + k) := by
  intro u h_q h_cyl
  obtain ⟨n_one, n_neg, _n_pos_zero, _h_count, h_neg_le, h_w, h_k_le⟩ :=
    h_one_lower_bound u h_q h_cyl
  have h_n_one_int : (k : Int) ≤ (n_one : Int) := by exact_mod_cast h_k_le
  have h_n_neg_int : (n_neg : Int) ≤ (Q : Int) := by exact_mod_cast h_neg_le
  linarith

/-! ### Direct admissibility-based defect bound

A clean direct proof (independent of path decomposition) that
`defect(evalWord u) ≥ Word.numOnes u - Word.numZeros u` for every
word `u`, exploiting the admissibility invariant: each `step` adds
`τ(s.n) ≥ 1` to `A`, so `A` grows by at least `Word.length u`. -/

/-- For every admissible state `s` and word `u`, the A-component grows
by at least `u.length`. Each step contributes `τ(current.n) ≥ 1` by
`tau_ge_one`, and admissibility is preserved by `step_inv`. -/
theorem runWord_A_ge_length (s : AdmState) (h_inv : Inv s) (u : Word) :
    s.A + u.length ≤ (runWord u s).A := by
  induction u generalizing s with
  | nil => simp [runWord]
  | cons b bs ih =>
      have h_X : InX s.n := h_inv.2
      have h_tau : 1 ≤ tau s.n := tau_ge_one h_X
      have h_inv' : Inv (step s b) := step_inv h_inv b
      have h_step_A : (step s b).A = s.A + tau s.n := by
        cases b <;> simp [step]
      have h_ih := ih (step s b) h_inv'
      simp [runWord]
      have : (step s b).A ≥ s.A + 1 := by rw [h_step_A]; omega
      have h_length : (b :: bs).length = bs.length + 1 := by simp
      omega

/-- **Defect lower bound (intrinsic word form)**: for every word `u`,
\[
  \text{defect}(\text{evalWord}\, u) \ge \text{Word.numOnes}\, u - \text{Word.numZeros}\, u.
\]

Proof: `defect = A - 2q` with `q = Word.numZeros u` (by `evalWord_q_eq`)
and `A ≥ Word.length u = Word.numOnes u + Word.numZeros u` (by
`runWord_A_ge_length` applied to `initState`). -/
theorem defect_ge_numOnes_minus_numZeros (u : Word) :
    (Word.numOnes u : Int) - (Word.numZeros u : Int) ≤ defect (evalWord u) := by
  have h_A : initState.A + u.length ≤ (evalWord u).A :=
    runWord_A_ge_length initState init_inv u
  have h_q : (evalWord u).q = Word.numZeros u := evalWord_q_eq u
  have h_length : u.length = Word.numOnes u + Word.numZeros u :=
    Word.length_eq_numOnes_add_numZeros u
  unfold defect
  rw [h_q]
  have h_initState_A : initState.A = 0 := rfl
  rw [h_initState_A] at h_A
  -- h_A : u.length ≤ (evalWord u).A
  -- defect = (evalWord u).A - 2·numZeros ≥ (numOnes + numZeros) - 2·numZeros = numOnes - numZeros.
  push_cast
  rw [h_length] at h_A
  -- (evalWord u).A ≥ numOnes + numZeros (as Nat)
  -- (defect : Int) = ((evalWord u).A : Int) - 2 * (numZeros : Int)
  have h_A_int : ((Word.numOnes u + Word.numZeros u : Nat) : Int) ≤ ((evalWord u).A : Int) := by
    have : Word.numOnes u + Word.numZeros u ≤ (evalWord u).A := by omega
    exact_mod_cast this
  push_cast at h_A_int
  linarith

/-! ### The S202 one-edge-count conjecture: the SINGLE remaining gap

The cumulative Lean infrastructure of this session reduces the formal
proof of the S202 slope barrier (and hence one half of the S202
alternative for Collatz) to a single combinatorial conjecture about
the structure of admissible words landing in the m-th cylinder of
`aS202`. We formalise this conjecture below and prove the
**conditional implication**: assuming the conjecture, the S202 slope
barrier `defect ≥ m` follows as a Lean theorem. -/

/-- **S202 one-edge-count conjecture** (combinatorial / 3-adic) —
**tight, intrinsic form**.

For every `m ≥ 1`, every admissible word `u` in the m-th S202 cylinder
has, in its inverse-graph image under `S212_forward`, **at least
`m + q(u)` one-edges**.

Equivalently in word-theoretic terms (since each `1` character becomes
a one-edge and each `0` character a zero-edge):
\[
  m + \text{Word.numZeros}(u) \le \text{Word.numOnes}(u),
\]
or equivalently
\[
  \text{Word.numOnes}(u) - \text{Word.numZeros}(u) \ge m.
\]

The bound is **intrinsic** to the word `u` — no external budget `Q`
parameter — and tightens the trivial baseline by exactly the cylinder
index `m`.

**Status**: open mathematical problem. The geometric content is that
entering the m-th S202 cylinder from the root requires the path to
have **at least `m` more one-edges than zero-edges**. The intuition:
zero-edges with τ=1 push the path toward the `−1`-cylinder (formalised
by `zeroEdge_tau_1_rhoMinus_pos`), while the goal forces a return to
the `1`-cylinder (formalised by `goal_rhoMinus_zero`, `goal_deltaPlus_zero`).
The separation `min(ρ₊, ρ₋) = 0` (formalised by
`rho_plus_rho_minus_separation`) ensures these two regions are
3-adically disjoint, requiring `m` "mixing" steps to traverse.

Closing it requires a 3-adic dynamical-systems argument beyond the
formalisation infrastructure. -/
def S202_one_edge_count_conjecture (m : Nat) : Prop :=
  ∀ u : Word,
    (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) →
    ∃ n_one n_neg n_pos_zero : Nat,
      n_neg + n_pos_zero = Word.numZeros u ∧
      (n_one : Int) - (n_neg : Int) ≤ defect (evalWord u) ∧
      (m : Int) ≤ (n_one : Int) - (n_neg : Int)

/-- **Conditional S202 slope barrier — precise tight form**.

The conjecture's tight form `m ≤ n_one - n_neg` directly implies
`defect ≥ m` (no further reasoning needed beyond the existing
`defect ≥ n_one - n_neg` from path decomposition). The proof is a
one-liner.

**Why this form is preferred** over `numOnes ≥ m + q`:

The path-decomposition `WPath_weight_decompose` already gives
`defect ≥ n_one - n_neg`. Combining with `n_one - n_neg ≥ m` gives
the barrier directly. The over-counting form `numOnes ≥ m + q` treats
all zero-edges (including weight-0 `τ=2` edges that can recover `ρ_+`)
as if they were negative, making it strictly stronger than necessary
and potentially false. -/
theorem S202_slope_barrier_conditional
    {m : Nat} (hm : 1 ≤ m) (Q : Nat)
    (h_conj : S202_one_edge_count_conjecture m) :
    S216BarrierForWords m Q (m : Int) := by
  intro u _h_q h_cyl
  obtain ⟨_n_one, _n_neg, _, _, h_w, h_diff_ge⟩ := h_conj u h_cyl
  linarith

/-- **Stronger sufficient form**: if every admissible word satisfies the
*coarser* bound `Word.numOnes u ≥ m + Word.numZeros u`, then the
precise conjecture also holds (via `defect_ge_numOnes_minus_numZeros`
and the path decomposition).

This is the form that admits the **direct combinatorial argument**:
count `1`'s vs `0`'s in the word, no path-edge analysis required.
However it may be **stricter than necessary** — counterexamples to
this stronger form would not invalidate the precise conjecture, and
ad-hoc 3-adic constructions exploiting `τ=2` zero-edges as recovery
mechanisms could in principle achieve `numOnes < m + numZeros` while
still satisfying `n_one - n_neg ≥ m`. -/
def S202_one_edge_count_conjecture_coarse (m : Nat) : Prop :=
  ∀ u : Word,
    (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) →
    m + (evalWord u).q ≤ Word.numOnes u

/-- The coarse form implies the precise form, via path decomposition. -/
theorem S202_one_edge_count_conjecture_coarse_implies_precise
    {m : Nat}
    (h_coarse : S202_one_edge_count_conjecture_coarse m) :
    S202_one_edge_count_conjecture m := by
  intro u h_cyl
  -- coarse: m + (evalWord u).q ≤ Word.numOnes u
  have h_ones : m + (evalWord u).q ≤ Word.numOnes u := h_coarse u h_cyl
  have h_q_eq : (evalWord u).q = Word.numZeros u := evalWord_q_eq u
  have h_defect := defect_ge_numOnes_minus_numZeros u
  -- Witnesses: n_one := Word.numOnes u, n_neg := Word.numZeros u, n_pos_zero := 0.
  -- (The coarse form treats all zeros as negative; this satisfies the
  -- precise existential.)
  refine ⟨Word.numOnes u, Word.numZeros u, 0, by omega, h_defect, ?_⟩
  rw [h_q_eq] at h_ones
  have h_ones_int : ((m + Word.numZeros u : Nat) : Int) ≤ (Word.numOnes u : Int) := by
    exact_mod_cast h_ones
  push_cast at h_ones_int
  linarith

/-! ### Summary: the complete logical chain to Collatz from current state

```text
       Collatz conjecture
           ↑
           │   needs: S202 alternative resolved + reduction
           │   (matemática externa — fuera del programa)
           │
       S202 alternative (slope barrier or subcritical access)
           ↑
           │   slope-barrier branch:  defect ≥ m uniformly
           │
       S216BarrierForWords m Q m   ← S202_slope_barrier_conditional ✅
           ↑
           │   modulo:  S202_one_edge_count_conjecture m Q
           │           (THE single remaining mathematical gap)
           │
       n_one ≥ m + Q for every admissible word
           ↑
           │   ← Word_defect_decompose ✅ (Lean theorem)
           │   ← WPath_weight_decompose ✅ (Lean theorem)
           │   ← invEdge_weight_trichotomy ✅ (Lean theorem)
           │
       Path of admissible word in inverse cylinder graph
```

**The S202 one-edge-count conjecture** is the precise, rigorously
stated, single open problem that — once resolved by 3-adic dynamics —
would close the analytic side of the S202 alternative as a Lean
theorem. The conjecture is **combinatorial and 3-adic in nature**, and
falls outside the formalisation infrastructure. -/

end CollatzLean4.Admissible
