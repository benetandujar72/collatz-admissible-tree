/-
**κ-precise Bellman-Ford certificate pipeline.**

Decidable (`outgoingEdges`-based) analogue of the S216 closure machinery, but
with the κ-precise edge weights (one-edge +1, τ=1 zero-edge −1, τ≥2 zero-edge 0)
instead of the actual defect weights. Reuses the proven `outgoingEdges`
enumerator and its completeness lemmas; the κ-weight of an enumerated edge
`(v', ω)` is recovered computably by `toKappa v v' ω`.

The terminal theorem `S216_barrier_for_words_via_kappa` takes a κ-weighted
optimistic-closure certificate (three native_decide-checkable fields) and
concludes `m ≤ defect(u)` for every admissible word `u` in the m-th S202
cylinder with `q(u) ≤ Q` — via the chain

  κ-cert  →  no goal reachable with κ-cost < m  →  n_one − n_neg ≥ m
          →  defect ≥ n_one − n_neg ≥ m.

This is the κ-weighted, non-circular counterpart of
`S216_barrier_for_words_outgoing`.
-/

import CollatzLean4.AnalyticBarrier
import CollatzLean4.S216

namespace CollatzLean4.Admissible

/-- Recover the κ-precise weight of an `outgoingEdges` entry `(v', ω)` from the
source `v`: one-edges (`v'.j = v.j`) weigh `+1`; zero-edges (`v'.j = v.j+1`)
weigh `−1` when `ω = -1` (i.e. `τ = 1`) and `0` otherwise (`τ ≥ 2`). -/
def toKappa (v v' : InvVertex) (ω : Int) : Int :=
  if v'.j = v.j then 1 else if ω = -1 then -1 else 0

/-- Every κ-precise edge has an underlying `InvEdge` of actual weight `ω`, with
`κ = toKappa v v' ω`. This is the bridge between the κ-path and the computable
`outgoingEdges` enumeration. -/
theorem InvKappaPreciseEdge_toKappa
    {R : Nat} {v v' : InvVertex} {κ : Int}
    (h : InvKappaPreciseEdge R v v' κ) :
    ∃ ω, InvEdge R v v' ω ∧ κ = toKappa v v' ω := by
  rcases h with ⟨ω, h_e, h_k⟩ | ⟨ω, h_e, h_tau, h_k⟩ | ⟨ω, h_e, h_tau, h_k⟩
  · refine ⟨ω, Or.inl h_e, ?_⟩
    obtain ⟨h_j, _, _, _⟩ := h_e
    subst h_k
    simp only [toKappa, if_pos h_j]
  · refine ⟨ω, Or.inr h_e, ?_⟩
    obtain ⟨h_j, _, _, h_ω⟩ := h_e
    subst h_k
    have h_jne : ¬ (v'.j = v.j) := by omega
    have h_ωm1 : ω = -1 := by rw [h_ω, h_tau]; norm_num
    simp only [toKappa, if_neg h_jne, if_pos h_ωm1]
  · refine ⟨ω, Or.inr h_e, ?_⟩
    obtain ⟨h_j, _, _, h_ω⟩ := h_e
    subst h_k
    have h_jne : ¬ (v'.j = v.j) := by omega
    have h_ωne : ¬ (ω = -1) := by
      rw [h_ω]
      have h2 : (2 : Int) ≤ (tau v'.c : Int) := by exact_mod_cast h_tau
      omega
    simp only [toKappa, if_neg h_jne, if_neg h_ωne]

/-- **κ dist propagation** along an `InvKappaPreciseEdge` path. Mirror of
`propagate_dist_outgoing`: each κ-step is translated to an `outgoingEdges`
entry (via `InvKappaPreciseEdge_toKappa` + the completeness lemmas), and the
κ-weighted optimistic closure `h_closed` propagates the dist by one edge. -/
theorem kappa_propagate_dist_via
    {R Q : Nat} {T : Int}
    (dist : InvVertex → Option Int)
    (h_closed : ∀ v d, dist v = some d → relevant Q T v d →
        ∀ e ∈ outgoingEdges R Q v, e.1.j ≤ Q →
          relevant Q T e.1 (d + toKappa v e.1 e.2) →
          ∃ d', dist e.1 = some d' ∧ d' ≤ d + toKappa v e.1 e.2)
    {v_start t : InvVertex} {w d_v_start : Int} {vs : List InvVertex}
    (h_path : WPath (InvKappaPreciseEdge R) v_start t w vs)
    (hR : 1 ≤ R)
    (h_v_can : v_start.c < 3 ^ (R + v_start.j))
    (h_path_can : ∀ u ∈ vs, u.c < 3 ^ (R + u.j))
    (h_v_bound : v_start.j ≤ Q)
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q)
    (h_v_dist : dist v_start = some d_v_start)
    (h_total_lt : d_v_start + w < T) :
    ∃ d_t, dist t = some d_t ∧ d_t ≤ d_v_start + w := by
  induction vs generalizing v_start w d_v_start with
  | nil =>
      simp only [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      exact ⟨d_v_start, h_v_dist, by linarith⟩
  | cons u vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨κ₁, κ₂, h_kedge, h_rest, rfl⟩ := h_path
      have h_u_bound : u.j ≤ Q := h_path_bound u (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_bound : ∀ x ∈ vs', x.j ≤ Q := fun x hx =>
        h_path_bound x (List.mem_cons.mpr (Or.inr hx))
      have h_u_can : u.c < 3 ^ (R + u.j) :=
        h_path_can u (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_can : ∀ x ∈ vs', x.c < 3 ^ (R + x.j) := fun x hx =>
        h_path_can x (List.mem_cons.mpr (Or.inr hx))
      have h_suffix : -((Q : Int) - u.j) ≤ κ₂ :=
        abs_suffix_weight_bound Q
          (fun a b c hh => InvKappaPreciseEdge_weight_lower_bound hh)
          h_rest h_u_bound h_rest_bound
      have h_full_suffix : -((Q : Int) - v_start.j) ≤ κ₁ + κ₂ := by
        have h_full : WPath (InvKappaPreciseEdge R) v_start t (κ₁ + κ₂) (u :: vs') := by
          simp only [WPath]; exact ⟨κ₁, κ₂, h_kedge, h_rest, rfl⟩
        exact abs_suffix_weight_bound Q
          (fun a b c hh => InvKappaPreciseEdge_weight_lower_bound hh)
          h_full h_v_bound h_path_bound
      have h_v_rel : relevant Q T v_start d_v_start := by
        unfold relevant credit; linarith
      have h_u_rel : relevant Q T u (d_v_start + κ₁) := by
        unfold relevant credit; linarith
      obtain ⟨ω, h_invedge, h_kappa_eq⟩ := InvKappaPreciseEdge_toKappa h_kedge
      have hR_v : 1 ≤ R + v_start.j := by omega
      have h_in : (u, ω) ∈ outgoingEdges R Q v_start := by
        rcases h_invedge with h_one | h_zero
        · have h_u_j_eq : u.j = v_start.j := h_one.1
          have hu_can_R : u.c < 3 ^ (R + v_start.j) := by rw [← h_u_j_eq]; exact h_u_can
          exact outgoingEdges_complete_one R Q v_start u ω hu_can_R hR_v h_one
        · have h_u_j_eq : u.j = v_start.j + 1 := h_zero.1
          have hu_can_R : u.c < 3 ^ (R + v_start.j + 1) := by
            have h_idx : R + v_start.j + 1 = R + u.j := by omega
            rw [h_idx]; exact h_u_can
          have hv_jQ : v_start.j < Q := by omega
          exact outgoingEdges_complete_zero R Q v_start u ω hu_can_R hv_jQ h_zero
      have h_tk : toKappa v_start (u, ω).1 (u, ω).2 = κ₁ := h_kappa_eq.symm
      have h_u_rel' :
          relevant Q T (u, ω).1 (d_v_start + toKappa v_start (u, ω).1 (u, ω).2) := by
        rw [h_tk]; exact h_u_rel
      obtain ⟨d_u', h_u_dist, h_u_le⟩ :=
        h_closed v_start d_v_start h_v_dist h_v_rel (u, ω) h_in h_u_bound h_u_rel'
      rw [h_tk] at h_u_le
      have h_u_total_lt : d_u' + κ₂ < T := by linarith
      obtain ⟨d_t, h_t_dist, h_t_le⟩ :=
        ih h_rest h_u_can h_rest_can h_u_bound h_rest_bound h_u_dist h_u_total_lt
      exact ⟨d_t, h_t_dist, by linarith⟩

/-- **κ closure-to-barrier**: a κ-path of κ-cost `< T` from the cert start to a
goal yields `False`. -/
theorem kappa_closure_to_barrier_via
    {R Q : Nat} {T : Int}
    (dist : InvVertex → Option Int) (start : InvVertex)
    (h_start_dist : dist start = some 0)
    (h_no_goal : ∀ v d, dist v = some d → InvVertex.IsGoal v R → ¬ d < T)
    (h_closed : ∀ v d, dist v = some d → relevant Q T v d →
        ∀ e ∈ outgoingEdges R Q v, e.1.j ≤ Q →
          relevant Q T e.1 (d + toKappa v e.1 e.2) →
          ∃ d', dist e.1 = some d' ∧ d' ≤ d + toKappa v e.1 e.2)
    (hR : 1 ≤ R)
    (h_start_can : start.c < 3 ^ (R + start.j))
    {goal : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvKappaPreciseEdge R) start goal w vs)
    (h_g : InvVertex.IsGoal goal R)
    (h_start_bound : start.j ≤ Q)
    (h_path_can : ∀ u ∈ vs, u.c < 3 ^ (R + u.j))
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q)
    (h_w_lt : w < T) :
    False := by
  obtain ⟨d_goal, h_goal_dist, h_goal_le⟩ :=
    kappa_propagate_dist_via dist h_closed h_path hR h_start_can h_path_can
      h_start_bound h_path_bound h_start_dist (by linarith)
  exact h_no_goal goal d_goal h_goal_dist h_g (by linarith)

/-- **κ-weighted cylinder barrier for words.** Given a κ-weighted
optimistic-closure certificate (`dist` with start dist 0, no goal below `m`, and
κ-weighted closure over `outgoingEdges`), every admissible word `u` with
`q(u) ≤ Q` landing in the m-th S202 cylinder has `defect(u) ≥ m`.

This unfolds to `S216BarrierForWords m Q m` — the κ route. -/
theorem S216_barrier_for_words_via_kappa
    {m Q : Nat}
    (dist : InvVertex → Option Int)
    (h_start_dist : dist (InvStart m) = some 0)
    (h_no_goal : ∀ v d, dist v = some d →
        InvVertex.IsGoal v (22 * m + 2) → ¬ d < (m : Int))
    (h_closed : ∀ v d, dist v = some d → relevant Q (m : Int) v d →
        ∀ e ∈ outgoingEdges (22 * m + 2) Q v, e.1.j ≤ Q →
          relevant Q (m : Int) e.1 (d + toKappa v e.1 e.2) →
          ∃ d', dist e.1 = some d' ∧ d' ≤ d + toKappa v e.1 e.2)
    (u : Word)
    (h_q : (evalWord u).q ≤ Q)
    (h_cyl : (evalWord u).n % (3 ^ (22 * m + 2))
              = aS202 % (3 ^ (22 * m + 2))) :
    (m : Int) ≤ defect (evalWord u) := by
  obtain ⟨vs, goal, h_g, h_goal_j, h_can, h_path_inv⟩ := S212_forward m u h_cyl
  have h_numZeros_le : Word.numZeros u ≤ Q := by rw [← evalWord_q_eq]; exact h_q
  have h_goal_j_le : goal.j ≤ Q := by rw [h_goal_j]; exact h_numZeros_le
  have h_mono := WPath_j_monotone h_path_inv
  have h_vs_bound : ∀ x ∈ vs, x.j ≤ Q := fun x hx => by
    have := h_mono.2 x hx; omega
  obtain ⟨n_one, n_neg, n_pos_zero, h_counts⟩ := WPath.exists_InvPathCounts h_path_inv
  have h_wlb : (n_one : Int) - (n_neg : Int) ≤ defect (evalWord u) :=
    InvPathCounts.weight_lower_bound h_counts
  by_contra h_not
  rw [not_le] at h_not
  have h_kw_lt : (n_one : Int) - (n_neg : Int) < (m : Int) :=
    lt_of_le_of_lt h_wlb h_not
  have h_kpath := InvPathCounts.toKappaWPath h_counts
  have h_start_can : (InvStart m).c < 3 ^ (22 * m + 2 + (InvStart m).j) := by
    have h1 : (InvStart m).c = aS202 % 3 ^ (22 * m + 2) := rfl
    have h2 : (InvStart m).j = 0 := rfl
    rw [h1, h2, Nat.add_zero]
    exact Nat.mod_lt _ (by positivity)
  exact kappa_closure_to_barrier_via dist (InvStart m) h_start_dist h_no_goal
    h_closed (by omega : 1 ≤ 22 * m + 2) h_start_can h_kpath h_g
    (by show (0 : Nat) ≤ Q; exact Nat.zero_le Q) h_can h_vs_bound h_kw_lt

end CollatzLean4.Admissible
