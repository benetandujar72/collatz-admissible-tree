/-
Copyright (c) 2026 Benet Andújar Guardado.

S239 — Closed walks in the inverse cylinder graph: the j-stratification and the
order-of-2 (discrete-log) characterization. HONEST scope marking.

The proposed "closed-walk ↔ forward Collatz cycle" bridge does NOT hold, and this
file replaces it with the correct, verified characterization.

Finding. The inverse graph is LAYERED by `j`: `InvEdgeOne` keeps `j`, `InvEdgeZero`
increments it. Hence `j` is non-decreasing along every path (`WPath_j_le`), and a
CLOSED walk (returning to its start vertex) can use NO zero-edges — it is a pure
one-edge loop. Such a loop telescopes the one-edge residue condition to
    v₀.c ≡ 2^W · v₀.c    (mod 3^{R+j}),
and since `v₀.c` is admissible hence a unit mod 3^k, this forces
    2^W ≡ 1              (mod 3^{R+j}).
So closed walks do NOT encode forward Collatz cycles (the graph is acyclic across
j-levels); they encode the multiplicative ORDER OF 2 mod 3^k — the very
discrete-log structure at the heart of the slope-barrier slack. Forward
cycle-exclusion lives in the forward Syracuse framework (`CycleEquation.lean`),
not here. 0 sorry / 0 ad-hoc axiom.
-/

import CollatzLean4.InverseGraph
import CollatzLean4.PotentialBarrier
import CollatzLean4.LTEBound

namespace CollatzLean4.Admissible

/-! ### j-stratification: `j` is non-decreasing along inverse paths -/

/-- Every inverse edge is `j`-non-decreasing (one-edge keeps `j`, zero-edge
increments it). -/
theorem InvEdge_j_le {R : Nat} {v v' : InvVertex} {ω : Int}
    (h : InvEdge R v v' ω) : v.j ≤ v'.j := by
  rcases h with h | h
  · have : v'.j = v.j := h.1; omega
  · have : v'.j = v.j + 1 := h.1; omega

/-- `j` is non-decreasing along any inverse-graph path. The graph is a DAG across
`j`-levels. -/
theorem WPath_j_le {R : Nat} :
    ∀ {s t : InvVertex} {w : Int} {vs : List InvVertex},
      WPath (InvEdge R) s t w vs → s.j ≤ t.j := by
  intro s t w vs h
  induction vs generalizing s w with
  | nil =>
      simp only [WPath] at h
      obtain ⟨rfl, _⟩ := h
      exact le_refl _
  | cons v vs ih =>
      simp only [WPath] at h
      obtain ⟨ω₁, ω₂, h_edge, h_rest, _⟩ := h
      exact le_trans (InvEdge_j_le h_edge) (ih h_rest)

/-! ### One-edge walks: residue telescoping -/

/-- **One-edge residue telescoping.** A one-edge walk keeps `j` and accumulates
the residue relation `s.c ≡ 2^W · t.c (mod 3^{R+j})`, where `W` is the total
weight (a nonnegative integer). -/
theorem oneWalk_residue {R : Nat} :
    ∀ {s t : InvVertex} {w : Int} {vs : List InvVertex},
      WPath (InvEdgeOne R) s t w vs →
      s.j = t.j ∧ ∃ E : Nat, (E : Int) = w ∧
        s.c % 3 ^ (R + s.j) = (2 ^ E * t.c) % 3 ^ (R + s.j) := by
  intro s t w vs h
  induction vs generalizing s w with
  | nil =>
      simp only [WPath] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, 0, by norm_num, by simp⟩
  | cons v vs ih =>
      simp only [WPath] at h
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h
      obtain ⟨hj_sv, _hX_v, hcong, hω₁⟩ := h_edge
      obtain ⟨hj_vt, E, hE, hEcong⟩ := ih h_rest
      refine ⟨by omega, tau v.c + E, ?_, ?_⟩
      · rw [hω₁, ← hE]; push_cast; ring
      · have hM : R + v.j = R + s.j := by omega
        have e1 : s.c ≡ 2 ^ tau v.c * v.c [MOD 3 ^ (R + s.j)] := hcong
        have e2 : v.c ≡ 2 ^ E * t.c [MOD 3 ^ (R + s.j)] := by
          rw [hM] at hEcong; exact hEcong
        have e3 := Nat.ModEq.mul_left (2 ^ tau v.c) e2
        have e5 := e1.trans e3
        have e4 : 2 ^ tau v.c * (2 ^ E * t.c) = 2 ^ (tau v.c + E) * t.c := by
          rw [pow_add]; ring
        rw [e4] at e5
        exact e5

/-! ### Admissible residues are units mod 3^k -/

/-- An admissible residue is coprime to `3^k` (since `c mod 9 ∈ X` ⟹ `3 ∤ c`). -/
theorem InX_coprime_three_pow {c : Nat} (h : InX c) (k : Nat) :
    Nat.Coprime c (3 ^ k) := by
  have h3 : ¬ (3 ∣ c) := by unfold InX at h; omega
  have hcop : Nat.Coprime 3 c := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
  exact (hcop.symm).pow_right k

/-! ### Closed walks encode the order of 2 (NOT forward cycles) -/

/-- **Closed one-edge walks encode the order of 2.** A closed one-edge walk
returning to an admissible vertex `v₀` forces `2^W ≡ 1 (mod 3^{R+j})`, where `W`
is the total weight. No forward Collatz cycle is encoded — the inverse graph is
`j`-acyclic; this is a discrete-log / order-of-2 constraint, the same structure
underlying the slope-barrier slack. -/
theorem closed_oneWalk_two_pow_mod {R : Nat} {v₀ : InvVertex} {w : Int}
    {vs : List InvVertex} (hX : InX v₀.c)
    (h : WPath (InvEdgeOne R) v₀ v₀ w vs) :
    ∃ E : Nat, (E : Int) = w ∧
      (2 ^ E) % 3 ^ (R + v₀.j) = 1 % 3 ^ (R + v₀.j) := by
  obtain ⟨_hj, E, hE, hcong⟩ := oneWalk_residue h
  refine ⟨E, hE, ?_⟩
  have hcop : Nat.Coprime v₀.c (3 ^ (R + v₀.j)) := InX_coprime_three_pow hX _
  have hmod : 1 * v₀.c ≡ 2 ^ E * v₀.c [MOD 3 ^ (R + v₀.j)] := by
    rw [one_mul]; exact hcong
  exact (Nat.ModEq.cancel_right_of_coprime hcop.symm hmod).symm

/-! ### The order of 2 is astronomically large: closed-walk weight bound -/

/-- **Closed-walk weight is astronomically large.** A nontrivial closed one-edge
walk (`0 < w`) at cylinder depth `k = R + j ≥ 1` has total weight
`w ≥ 2·3^{k−1}` — a multiple of the multiplicative order of 2 mod 3^k. This
REUSES the project's LTE law `padicValNat_two_pow_sub_one` and exposes, on the
closed-walk side, the same astronomical slack that obstructs the slope barrier:
any genuine loop in the inverse graph is exponentially long. -/
theorem closed_oneWalk_weight_ge_order {R : Nat} {v₀ : InvVertex} {w : Int}
    {vs : List InvVertex} (hX : InX v₀.c) (hk : 1 ≤ R + v₀.j) (hpos : 0 < w)
    (h : WPath (InvEdgeOne R) v₀ v₀ w vs) :
    (2 * 3 ^ (R + v₀.j - 1) : Int) ≤ w := by
  obtain ⟨E, hEw, hmod⟩ := closed_oneWalk_two_pow_mod hX h
  have hE0 : E ≠ 0 := by
    intro h0; rw [h0] at hEw; simp only [Nat.cast_zero] at hEw; omega
  have h1le : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hdvd : 3 ^ (R + v₀.j) ∣ (2 ^ E - 1) :=
    (Nat.modEq_iff_dvd' h1le).mp hmod.symm
  have h2E0 : 2 ^ E - 1 ≠ 0 := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hE0)
    simp only [pow_one] at h2; omega
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hkle : R + v₀.j ≤ padicValNat 3 (2 ^ E - 1) := by
    rw [← Nat.factorization_def _ hp3]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp3 h2E0).mp hdvd
  rw [padicValNat_two_pow_sub_one E hE0] at hkle
  by_cases hev : Even E
  · rw [if_pos hev] at hkle
    have hk1 : R + v₀.j - 1 ≤ padicValNat 3 E := by omega
    have hdvd3 : 3 ^ (R + v₀.j - 1) ∣ E := by
      rw [← Nat.factorization_def _ hp3] at hk1
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp3 hE0).mpr hk1
    have hdvd2 : 2 ∣ E := hev.two_dvd
    have hcop : Nat.Coprime 2 (3 ^ (R + v₀.j - 1)) :=
      (by decide : Nat.Coprime 2 3).pow_right _
    have hdvd6 : 2 * 3 ^ (R + v₀.j - 1) ∣ E :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd2 hdvd3
    have hle : 2 * 3 ^ (R + v₀.j - 1) ≤ E :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hE0) hdvd6
    calc (2 * 3 ^ (R + v₀.j - 1) : Int) ≤ (E : Int) := by exact_mod_cast hle
      _ = w := hEw
  · rw [if_neg hev] at hkle
    exfalso; omega

end CollatzLean4.Admissible
