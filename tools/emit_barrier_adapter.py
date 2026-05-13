"""
Emits the Bool→Prop adapter + terminal barrier theorem for a given
(m, Q) certificate. Companion to cert_to_lean_s216.py.

Usage:
  python tools/emit_barrier_adapter.py <m> <Q>
    > CollatzLean4/CollatzLean4/Cert_m{m}_Q{Q}_S216_Barrier.lean
"""
from __future__ import annotations
import sys


def emit_barrier_adapter(m: int, Q: int, T: int = 1) -> str:
    R = 22 * m + 2
    p = f"m{m}_Q{Q}"  # name suffix
    ns_cert = f"Cert_m{m}_Q{Q}_S216"
    return f"""/-
**Terminal barrier theorem `Cert_m{m}_Q{Q}_S216.barrier_m{m}_Q{Q}`**
   : `S216BarrierForWords {m} {Q} {T}`

Auto-generated Bool→Prop adapter for the auto-generated certificate
`Cert_m{m}_Q{Q}_S216.lean`. The pattern is identical to
`Cert_m1_Q3_S216_Barrier.lean` (Front 1 prototype) up to renaming.

Resulting theorem (formal statement of `𝒞^←_{{S202}}({m}, {Q}) ≥ {T}`):

  ∀ u : Word, (evalWord u).q ≤ {Q} →
    (evalWord u).n % 3^{R} = aS202 % 3^{R} →
    {T} ≤ defect (evalWord u)
-/

import CollatzLean4.Cert_m{m}_Q{Q}_S216
import CollatzLean4.S216

namespace CollatzLean4.Admissible.Certificates

open CollatzLean4.Admissible

/-- Membership extraction from the partial dist function. -/
lemma dist_some_mem_tbl_{p} {{v : InvVertex}} {{d : Int}}
    (h : cert_{p}_S216_dist v = some d) :
    (v, d) ∈ cert_{p}_S216_tbl := by
  unfold cert_{p}_S216_dist at h
  rcases h_eq : cert_{p}_S216_tbl.find? (·.1 = v) with _ | ⟨v', d'⟩
  · rw [h_eq] at h; simp at h
  · rw [h_eq] at h
    simp at h
    have h_pred := List.find?_some h_eq
    simp at h_pred
    subst h_pred
    subst h
    exact List.mem_of_find?_eq_some h_eq

theorem check_start_sound_{p}
    (h : cert_{p}_S216_start_check = true) :
    S216StartOK cert_{p}_S216_start cert_{p}_S216_dist := by
  unfold S216StartOK
  unfold cert_{p}_S216_start_check at h
  exact of_decide_eq_true h

theorem check_no_goal_sound_{p}
    (h : cert_{p}_S216_no_goal_check = true) :
    S216NoGoalBelowT {R} ({T} : Int) cert_{p}_S216_dist := by
  unfold S216NoGoalBelowT
  intro v d h_dist h_goal h_lt
  have h_mem := dist_some_mem_tbl_{p} h_dist
  unfold cert_{p}_S216_no_goal_check at h
  rw [List.all_eq_true] at h
  have h_p := h (v, d) h_mem
  unfold InvVertex.IsGoal at h_goal
  simp only [Bool.or_eq_true, Bool.not_eq_true',
             decide_eq_false_iff_not] at h_p
  exact h_p.elim (fun hg => hg h_goal) (fun hd => hd h_lt)

theorem check_closed_sound_{p}
    (h : cert_{p}_S216_closed_check = true) :
    S216OptimisticClosed {R} {Q} ({T} : Int) cert_{p}_S216_dist := by
  unfold S216OptimisticClosed
  intro v d h_dist h_v_rel e h_e_in h_e_j_le h_e_rel
  have h_v_mem := dist_some_mem_tbl_{p} h_dist
  unfold cert_{p}_S216_closed_check at h
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
  rcases h_dist_e : cert_{p}_S216_dist e.1 with _ | d'
  · exfalso
    rw [h_dist_e] at h_match
    simp at h_match
  · rw [h_dist_e] at h_match
    refine ⟨d', rfl, ?_⟩
    simpa using h_match

/-- Assembled `S216Cert_outgoing` instance. -/
def cert_outgoing_{p} : S216Cert_outgoing {R} {Q} ({T} : Int) :=
  S216Cert_outgoing.mk'
    cert_{p}_S216_start
    cert_{p}_S216_dist
    (check_start_sound_{p} cert_{p}_S216_start_holds)
    (check_no_goal_sound_{p} cert_{p}_S216_no_goal_holds)
    (check_closed_sound_{p} cert_{p}_S216_closed_holds)

/-- Terminal barrier in internal form (native modulus 3^{R}). -/
theorem barrier_{p}_internal (u : Word)
    (h_q_bound : (evalWord u).q ≤ {Q})
    (h_cyl : (evalWord u).n % (3 ^ {R}) = aS202 % (3 ^ {R})) :
    ({T} : Int) ≤ defect (evalWord u) := by
  have h_start_match : cert_outgoing_{p}.start = InvStart {m} := rfl
  have h_start_can : cert_outgoing_{p}.start.c
                      < 3 ^ (22 * {m} + 2 + cert_outgoing_{p}.start.j) := by
    show (InvStart {m}).c < 3 ^ (22 * {m} + 2 + (InvStart {m}).j)
    unfold InvStart
    simp
    decide
  have h_cyl' : (evalWord u).n % (3 ^ (22 * {m} + 2))
                  = aS202 % (3 ^ (22 * {m} + 2)) := by
    have : 22 * {m} + 2 = {R} := by norm_num
    rw [this]; exact h_cyl
  exact S216_barrier_for_words_outgoing cert_outgoing_{p} h_start_match
    h_start_can u h_q_bound h_cyl'

end CollatzLean4.Admissible.Certificates

namespace {ns_cert}

open CollatzLean4.Admissible
open CollatzLean4.Admissible.Certificates

/-- **`{ns_cert}.barrier_{p} : S216BarrierForWords {m} {Q} {T}`** —
formal cylinder accessibility barrier `𝒞^←_{{S202}}({m}, {Q}) ≥ {T}`. -/
theorem barrier_{p} : S216BarrierForWords {m} {Q} {T} := by
  intro u h_q h_cyl
  exact barrier_{p}_internal u h_q h_cyl

end {ns_cert}
"""


if __name__ == "__main__":
    if len(sys.argv) not in (3, 4):
        print("Usage: python emit_barrier_adapter.py <m> <Q> [T]",
              file=sys.stderr)
        sys.exit(1)
    m, Q = int(sys.argv[1]), int(sys.argv[2])
    T = int(sys.argv[3]) if len(sys.argv) == 4 else 1
    sys.stdout.write(emit_barrier_adapter(m, Q, T))
