/-
**Terminal barrier theorem for (m = 1, Q = 3, T = 1)** — Front 1.

This module performs the Bool → Prop adapter mentioned in
HANDOFF_S216.md §3.2, lifting the auto-generated certificate
`cert_m1_Q3_S216_tbl` (proven via `native_decide`) to an
`S216Cert_outgoing` structure, and feeding it through
`S216_barrier_for_words_outgoing` to obtain the terminal theorem:

  `Cert_m1_Q3_S216.barrier_m1_Q3 : S216BarrierForWords 1 3 1`

which unfolds to

  `∀ u : Word, (evalWord u).q ≤ 3 →
       (evalWord u).n % 3^24 = aS202 % 3^24 →
       (1 : Int) ≤ defect (evalWord u)`.

Equivalent to `𝒞^←_{S202}(1, 3) ≥ 1` as a Lean theorem.

**Front 1 closure chain**

    Python certificate (s216_engine.py)
        ↓
    Cert_m1_Q3_S216.lean           (35-state BF table, 3 Bool checks)
        ↓
    native_decide                  (cert_m1_Q3_S216_*_holds)
        ↓
    check_start_sound              (Bool → S216StartOK)
    check_no_goal_sound            (Bool → S216NoGoalBelowT)
    check_closed_sound             (Bool → S216OptimisticClosed)
        ↓
    S216Cert_outgoing.mk'          (cert_outgoing)
        ↓
    S216_barrier_for_words_outgoing
        ↓
    Cert_m1_Q3_S216.barrier_m1_Q3 : S216BarrierForWords 1 3 1
-/

import CollatzLean4.Cert_m1_Q3_S216
import CollatzLean4.S216

namespace CollatzLean4.Admissible.Certificates

open CollatzLean4.Admissible

/-! ### Membership extraction from the partial `dist` function -/

/-- If `cert_m1_Q3_S216_dist v = some d`, then the pair `(v, d)` is in
the certificate table. -/
lemma dist_some_mem_tbl {v : InvVertex} {d : Int}
    (h : cert_m1_Q3_S216_dist v = some d) :
    (v, d) ∈ cert_m1_Q3_S216_tbl := by
  unfold cert_m1_Q3_S216_dist at h
  rcases h_eq : cert_m1_Q3_S216_tbl.find? (·.1 = v) with _ | ⟨v', d'⟩
  · rw [h_eq] at h; simp at h
  · rw [h_eq] at h
    simp at h
    have h_pred := List.find?_some h_eq
    simp at h_pred
    subst h_pred
    subst h
    exact List.mem_of_find?_eq_some h_eq

/-! ### Soundness theorems: each `native_decide`-d Bool check entails
the corresponding named Prop invariant. -/

/-- **`check_start_sound`**: the Bool start-check implies `S216StartOK`. -/
theorem check_start_sound
    (h : cert_m1_Q3_S216_start_check = true) :
    S216StartOK cert_m1_Q3_S216_start cert_m1_Q3_S216_dist := by
  unfold S216StartOK
  unfold cert_m1_Q3_S216_start_check at h
  exact of_decide_eq_true h

/-- **`check_no_goal_sound`**: the Bool no-goal-check implies
`S216NoGoalBelowT 24 1`. -/
theorem check_no_goal_sound
    (h : cert_m1_Q3_S216_no_goal_check = true) :
    S216NoGoalBelowT 24 (1 : Int) cert_m1_Q3_S216_dist := by
  unfold S216NoGoalBelowT
  intro v d h_dist h_goal h_lt
  have h_mem := dist_some_mem_tbl h_dist
  unfold cert_m1_Q3_S216_no_goal_check at h
  rw [List.all_eq_true] at h
  have h_p := h (v, d) h_mem
  unfold InvVertex.IsGoal at h_goal
  simp only [Bool.or_eq_true, Bool.not_eq_true',
             decide_eq_false_iff_not] at h_p
  exact h_p.elim (fun hg => hg h_goal) (fun hd => hd h_lt)

/-- **`check_closed_sound`**: the Bool closure-check implies
`S216OptimisticClosed 24 3 1`. -/
theorem check_closed_sound
    (h : cert_m1_Q3_S216_closed_check = true) :
    S216OptimisticClosed 24 3 (1 : Int) cert_m1_Q3_S216_dist := by
  unfold S216OptimisticClosed
  intro v d h_dist h_v_rel e h_e_in h_e_j_le h_e_rel
  have h_v_mem := dist_some_mem_tbl h_dist
  unfold cert_m1_Q3_S216_closed_check at h
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
  rcases h_dist_e : cert_m1_Q3_S216_dist e.1 with _ | d'
  · exfalso
    rw [h_dist_e] at h_match
    simp at h_match
  · rw [h_dist_e] at h_match
    refine ⟨d', rfl, ?_⟩
    simpa using h_match

/-! ### Adapter: assemble the `S216Cert_outgoing` instance -/

/-- **`cert_outgoing`** — the `(m=1, Q=3, T=1)` S216 certificate as an
`S216Cert_outgoing` structure, built from the three named-Prop
soundness theorems via `S216Cert_outgoing.mk'`. -/
def cert_outgoing : S216Cert_outgoing 24 3 (1 : Int) :=
  S216Cert_outgoing.mk'
    cert_m1_Q3_S216_start
    cert_m1_Q3_S216_dist
    (check_start_sound cert_m1_Q3_S216_start_holds)
    (check_no_goal_sound cert_m1_Q3_S216_no_goal_holds)
    (check_closed_sound cert_m1_Q3_S216_closed_holds)

/-! ### Terminal barrier theorem -/

/-- **Terminal barrier theorem `barrier_m1_Q3`** (internal form, native
modulus `3^24`): every admissible word with at most 3 zero-steps,
whose representative lies in the first S202 cylinder, has defect ≥ 1. -/
theorem barrier_m1_Q3_internal (u : Word)
    (h_q_bound : (evalWord u).q ≤ 3)
    (h_cyl : (evalWord u).n % (3 ^ 24) = aS202 % (3 ^ 24)) :
    (1 : Int) ≤ defect (evalWord u) := by
  have h_start_match : cert_outgoing.start = InvStart 1 := rfl
  have h_start_can : cert_outgoing.start.c
                      < 3 ^ (22 * 1 + 2 + cert_outgoing.start.j) := by
    show (InvStart 1).c < 3 ^ (22 * 1 + 2 + (InvStart 1).j)
    unfold InvStart
    simp
    decide
  have h_cyl' : (evalWord u).n % (3 ^ (22 * 1 + 2))
                  = aS202 % (3 ^ (22 * 1 + 2)) := by
    have : 22 * 1 + 2 = 24 := by norm_num
    rw [this]; exact h_cyl
  exact S216_barrier_for_words_outgoing cert_outgoing h_start_match
    h_start_can u h_q_bound h_cyl'

end CollatzLean4.Admissible.Certificates

/-! ### Named export under `Cert_m1_Q3_S216` namespace

Front 1 acceptance criterion:
`#check Cert_m1_Q3_S216.barrier_m1_Q3 : S216BarrierForWords 1 3 1`. -/
namespace Cert_m1_Q3_S216

open CollatzLean4.Admissible
open CollatzLean4.Admissible.Certificates

/-- **`Cert_m1_Q3_S216.barrier_m1_Q3 : S216BarrierForWords 1 3 1`**

The first formal terminal cylinder accessibility barrier of the
Bandujar program. Establishes
`𝒞^←_{S202}(1, 3) ≥ 1` as a Lean theorem with 0 sorries and 0
axiomatic gaps beyond the standard Lean + Mathlib + native_decide
axioms (`propext`, `Classical.choice`, `Quot.sound`,
`native_decide.ax_*`). -/
theorem barrier_m1_Q3 : S216BarrierForWords 1 3 1 := by
  intro u h_q h_cyl
  exact barrier_m1_Q3_internal u h_q h_cyl

end Cert_m1_Q3_S216
