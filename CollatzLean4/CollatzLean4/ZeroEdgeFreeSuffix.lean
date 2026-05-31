/-
S240 — The zero-edge-free stratum of the Wall-B residual (provable positivity).

From the S240 κ-sign research synthesis (N3): since `j` is non-decreasing along a κ-precise
path (`InvKappaPreciseEdge_j_monotone`) and zero-edges raise `j` STRICTLY, a suffix with
`mid.j = goal.j` contains NO zero-edges — every edge is a one-edge (κ = +1).  Hence its κ-weight
equals the number of edges, so `κ₂ = vs₂.length`, and `κ₂ ≥ 1` whenever the suffix is nonempty.

This discharges the `mid.j = goal.j` stratum of `FirstMPrecisionSuffixPositive` unconditionally.
The remaining (hard) cases are exactly the zero-edge-bearing suffixes (`mid.j < goal.j`), where
the dlog=2 / c≡4 trap reachability is the open crux.

Pure list induction; axioms {propext, Quot.sound}.  Builds narrow.
-/

import CollatzLean4.AnalyticBarrier

namespace CollatzLean4.Admissible

/-- **Zero-edge-free suffix ⟹ κ₂ counts the edges.**  If a κ-precise path keeps the
zero-budget coordinate `j` fixed (`mid.j = goal.j`), then — since zero-edges strictly raise
`j` — every edge is a one-edge (κ = +1), so the total κ-weight equals the path length. -/
theorem zeroEdgeFreeSuffix_kappa_eq_length
    {R : Nat} {mid goal : InvVertex} {κ₂ : Int} {vs₂ : List InvVertex}
    (h_path : WPath (InvKappaPreciseEdge R) mid goal κ₂ vs₂)
    (hj : mid.j = goal.j) :
    κ₂ = (vs₂.length : Int) := by
  induction vs₂ generalizing mid κ₂ with
  | nil =>
      simp only [WPath] at h_path
      obtain ⟨_, rfl⟩ := h_path
      simp
  | cons v vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, hκ⟩ := h_path
      have h_mid_v : mid.j ≤ v.j := InvKappaPreciseEdge_j_monotone h_edge
      have h_v_goal : v.j ≤ goal.j := (WPath_kappa_j_monotone h_rest).1
      have hvj : v.j = goal.j := by omega
      -- The edge `mid → v` cannot be a zero-edge (those force `v.j = mid.j + 1`).
      have hω₁ : ω₁ = 1 := by
        rcases h_edge with h_one | h_zn | h_zp
        · obtain ⟨_ω, _he, hκ'⟩ := h_one
          exact hκ'
        · obtain ⟨_ω, he, _ht, _hκ'⟩ := h_zn
          obtain ⟨hjz, _, _, _⟩ := he
          omega
        · obtain ⟨_ω, he, _ht, _hκ'⟩ := h_zp
          obtain ⟨hjz, _, _, _⟩ := he
          omega
      have hrec : ω₂ = (vs'.length : Int) := ih h_rest hvj
      rw [hκ, hω₁, hrec]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-- **Zero-edge-free positivity.**  A nonempty κ-precise suffix that keeps `j` fixed has
`κ₂ ≥ 1` — the `mid.j = goal.j` stratum of `FirstMPrecisionSuffixPositive`, discharged. -/
theorem zeroEdgeFreeSuffix_kappa_ge_one
    {R : Nat} {mid goal : InvVertex} {κ₂ : Int} {vs₂ : List InvVertex}
    (h_path : WPath (InvKappaPreciseEdge R) mid goal κ₂ vs₂)
    (hj : mid.j = goal.j) (hne : vs₂ ≠ []) :
    (1 : Int) ≤ κ₂ := by
  rw [zeroEdgeFreeSuffix_kappa_eq_length h_path hj]
  have h1 : 1 ≤ vs₂.length := by
    cases vs₂ with
    | nil => exact absurd rfl hne
    | cons _ _ => simp only [List.length_cons]; omega
  exact_mod_cast h1

end CollatzLean4.Admissible
