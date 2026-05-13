/-
**Terminal barrier theorem `Cert_m1_Q10_S216.barrier_m1_Q10`**
   : `S216BarrierForWords 1 10 1`

Auto-generated Bool→Prop adapter for the auto-generated certificate
`Cert_m1_Q10_S216.lean`. The pattern is identical to
`Cert_m1_Q8_S216_Barrier.lean` up to renaming.

Resulting theorem (formal statement of `𝒞^←_{S202}(1, 10) ≥ 1`):

  ∀ u : Word, (evalWord u).q ≤ 10 →
    (evalWord u).n % 3^24 = aS202 % 3^24 →
    1 ≤ defect (evalWord u)
-/

import CollatzLean4.Cert_m1_Q10_S216
import CollatzLean4.S216

namespace CollatzLean4.Admissible.Certificates

open CollatzLean4.Admissible

/-- Membership extraction from the partial dist function. -/
lemma dist_some_mem_tbl_m1_Q10 {v : InvVertex} {d : Int}
    (h : cert_m1_Q10_S216_dist v = some d) :
    (v, d) ∈ cert_m1_Q10_S216_tbl := by
  unfold cert_m1_Q10_S216_dist at h
  rcases h_eq : cert_m1_Q10_S216_tbl.find? (·.1 = v) with _ | ⟨v', d'⟩
  · rw [h_eq] at h; simp at h
  · rw [h_eq] at h
    simp at h
    have h_pred := List.find?_some h_eq
    simp at h_pred
    subst h_pred
    subst h
    exact List.mem_of_find?_eq_some h_eq

theorem check_start_sound_m1_Q10
    (h : cert_m1_Q10_S216_start_check = true) :
    S216StartOK cert_m1_Q10_S216_start cert_m1_Q10_S216_dist := by
  unfold S216StartOK
  unfold cert_m1_Q10_S216_start_check at h
  exact of_decide_eq_true h

theorem check_no_goal_sound_m1_Q10
    (h : cert_m1_Q10_S216_no_goal_check = true) :
    S216NoGoalBelowT 24 (1 : Int) cert_m1_Q10_S216_dist := by
  unfold S216NoGoalBelowT
  intro v d h_dist h_goal h_lt
  have h_mem := dist_some_mem_tbl_m1_Q10 h_dist
  unfold cert_m1_Q10_S216_no_goal_check at h
  rw [List.all_eq_true] at h
  have h_p := h (v, d) h_mem
  unfold InvVertex.IsGoal at h_goal
  simp only [Bool.or_eq_true, Bool.not_eq_true',
             decide_eq_false_iff_not] at h_p
  exact h_p.elim (fun hg => hg h_goal) (fun hd => hd h_lt)

theorem check_closed_sound_m1_Q10
    (h : cert_m1_Q10_S216_closed_check = true) :
    S216OptimisticClosed 24 10 (1 : Int) cert_m1_Q10_S216_dist := by
  unfold S216OptimisticClosed
  intro v d h_dist h_v_rel e h_e_in h_e_j_le h_e_rel
  have h_v_mem := dist_some_mem_tbl_m1_Q10 h_dist
  unfold cert_m1_Q10_S216_closed_check at h
  rw [List.all_eq_true] at h
  have h_p_v := h (v, d) h_v_mem
  simp only [Bool.or_eq_true, Bool.not_eq_true',
             decide_eq_false_iff_not] at h_p_v
  rcases h_p_v with h_v_not_rel | h_inner
  · exfalso
    apply h_v_not_rel
    have := h_v_rel
    unfold relevant credit at this
    exact this
  rw [List.all_eq_true] at h_inner
  have h_e_p := h_inner e h_e_in
  simp only [Bool.or_eq_true, Bool.not_eq_true',
             decide_eq_false_iff_not] at h_e_p
  rcases h_e_p with (h_e_j_neg | h_e_not_rel) | h_match
  · exact (h_e_j_neg h_e_j_le).elim
  · have := h_e_rel
    unfold relevant credit at this
    exact (h_e_not_rel this).elim
  rcases h_dist_e : cert_m1_Q10_S216_dist e.1 with _ | d'
  · exfalso
    rw [h_dist_e] at h_match
    simp at h_match
  · rw [h_dist_e] at h_match
    refine ⟨d', rfl, ?_⟩
    simpa using h_match

/-- Assembled `S216Cert_outgoing` instance. -/
def cert_outgoing_m1_Q10 : S216Cert_outgoing 24 10 (1 : Int) :=
  S216Cert_outgoing.mk'
    cert_m1_Q10_S216_start
    cert_m1_Q10_S216_dist
    (check_start_sound_m1_Q10 cert_m1_Q10_S216_start_holds)
    (check_no_goal_sound_m1_Q10 cert_m1_Q10_S216_no_goal_holds)
    (check_closed_sound_m1_Q10 cert_m1_Q10_S216_closed_holds)

/-- Terminal barrier in internal form (native modulus 3^24). -/
theorem barrier_m1_Q10_internal (u : Word)
    (h_q_bound : (evalWord u).q ≤ 10)
    (h_cyl : (evalWord u).n % (3 ^ 24) = aS202 % (3 ^ 24)) :
    (1 : Int) ≤ defect (evalWord u) := by
  have h_start_match : cert_outgoing_m1_Q10.start = InvStart 1 := rfl
  have h_start_can : cert_outgoing_m1_Q10.start.c
                      < 3 ^ (22 * 1 + 2 + cert_outgoing_m1_Q10.start.j) := by
    show (InvStart 1).c < 3 ^ (22 * 1 + 2 + (InvStart 1).j)
    unfold InvStart
    simp
    decide
  have h_cyl' : (evalWord u).n % (3 ^ (22 * 1 + 2))
                  = aS202 % (3 ^ (22 * 1 + 2)) := by
    have : 22 * 1 + 2 = 24 := by norm_num
    rw [this]; exact h_cyl
  exact S216_barrier_for_words_outgoing cert_outgoing_m1_Q10 h_start_match
    h_start_can u h_q_bound h_cyl'

end CollatzLean4.Admissible.Certificates

namespace Cert_m1_Q10_S216

open CollatzLean4.Admissible
open CollatzLean4.Admissible.Certificates

/-- **`Cert_m1_Q10_S216.barrier_m1_Q10 : S216BarrierForWords 1 10 1`** —
formal cylinder accessibility barrier `𝒞^←_{S202}(1, 10) ≥ 1`. -/
theorem barrier_m1_Q10 : S216BarrierForWords 1 10 1 := by
  intro u h_q h_cyl
  exact barrier_m1_Q10_internal u h_q h_cyl

end Cert_m1_Q10_S216
