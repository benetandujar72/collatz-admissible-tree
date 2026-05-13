/-
S214-Core: structural lemmas for 3-adic accessibility potentials.

This module closes the only proven lemma of paper/s214_core_section.tex
that was not previously formalized: the root/negative separation lemma
stating that no 3-adic cylinder can simultaneously approach 1 and -1.

The other three proved S214-Core lemmas are already formalized
elsewhere in the development:

  * Lemma "Iterated negative branch" (L^k closed form):
      `Lnum_eq_three_pow_mul_Lk` in `NegativeRuns.lean`.
  * Lemma "Negative runs force v_3(n+1) ≥ k":
      `negative_run_integrality_iff` in `NegativeRuns.lean`.
  * Lemma "S202 root-distance deficit"
      (δ_+(a_{S202}, R_m) = 22m - 20):
      `deltaPlus_aS202_general` in `Potential.lean`.
  * Proposition "Dual barrier certificate":
      `LocalPotentialCertificate.barrier` in `PotentialBarrier.lean`.

The conjectures of S214-Core (S202 accessibility barrier, universal
subcritical accessibility barrier, subcritical reduction of
counter-examples) remain explicitly open and are NOT formalized here.
-/

import CollatzLean4.Potential

namespace CollatzLean4.Admissible

/-! ### Helper: `nu3 n c = 0` when `n % 3 ≠ 0`. -/

/-- `nu3 n c = 0` whenever `n` is not a multiple of `3`. Holds for any cap
`c` (including `c = 0`). -/
theorem nu3_eq_zero_of_mod_three_ne_zero (n c : Nat) (h : n % 3 ≠ 0) :
    nu3 n c = 0 := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact h (by decide)
  cases c with
  | zero => rfl
  | succ c =>
      unfold nu3
      rw [if_neg hn, if_neg h]

/-! ### S214-Core root/negative separation lemma -/

/-- **S214-Core Lemma (root/negative separation).**

For every `c : Nat` and every cap `r : Nat`,
\[
  \min(\rho_+(c, r),\ \rho_-(c, r)) = 0.
\]
A 3-adic cylinder cannot simultaneously approach `1` and `−1`.

*Proof.* Case-split on `c % 3`:

  * If `c ≡ 0 (mod 3)`, then `(c+1) % 3 = 1 ≠ 0`, so `nu3 (c+1) r = 0`
    and therefore `ρ_-(c, r) = 0`.
  * If `c ≡ 1 (mod 3)`, then `(c+1) % 3 = 2 ≠ 0`, so `ρ_-(c, r) = 0`.
  * If `c ≡ 2 (mod 3)`, then `c ≠ 1`, hence `ρ_+(c, r) = nu3 (c-1) r`,
    and `(c-1) % 3 = 1 ≠ 0`, so `ρ_+(c, r) = 0`.
-/
theorem rho_plus_rho_minus_separation (c r : Nat) :
    min (rhoPlus c r) (rhoMinus c r) = 0 := by
  have hmod : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · -- c ≡ 0 (mod 3): (c+1) % 3 = 1 ⇒ ρ_- = 0
    have h_rm : rhoMinus c r = 0 := by
      unfold rhoMinus
      exact nu3_eq_zero_of_mod_three_ne_zero (c + 1) r (by omega)
    simp [h_rm]
  · -- c ≡ 1 (mod 3): (c+1) % 3 = 2 ⇒ ρ_- = 0
    have h_rm : rhoMinus c r = 0 := by
      unfold rhoMinus
      exact nu3_eq_zero_of_mod_three_ne_zero (c + 1) r (by omega)
    simp [h_rm]
  · -- c ≡ 2 (mod 3): c ≠ 1, (c-1) % 3 = 1 ⇒ ρ_+ = 0
    have hne : c ≠ 1 := by omega
    have h_rp : rhoPlus c r = 0 := by
      unfold rhoPlus
      rw [if_neg hne]
      exact nu3_eq_zero_of_mod_three_ne_zero (c - 1) r (by omega)
    simp [h_rp]

/-! ### Quantitative corollaries -/

/-- Corollary of the separation lemma: if `ρ_+(c, r) > 0` then
`ρ_-(c, r) = 0`.

Interpretation: paths that approach the root `1` cannot also exploit
long negative defect runs (which require proximity to `−1`). -/
theorem rhoMinus_eq_zero_of_rhoPlus_pos
    (c r : Nat) (h : 0 < rhoPlus c r) :
    rhoMinus c r = 0 := by
  have h_sep := rho_plus_rho_minus_separation c r
  by_contra h_ne
  have h_pos : 0 < rhoMinus c r := Nat.pos_of_ne_zero h_ne
  have : 0 < min (rhoPlus c r) (rhoMinus c r) := lt_min h h_pos
  omega

/-- Corollary of the separation lemma: if `ρ_-(c, r) > 0` then
`ρ_+(c, r) = 0`.

Interpretation: paths approaching the negative-run region cannot also
approach the root. -/
theorem rhoPlus_eq_zero_of_rhoMinus_pos
    (c r : Nat) (h : 0 < rhoMinus c r) :
    rhoPlus c r = 0 := by
  have h_sep := rho_plus_rho_minus_separation c r
  by_contra h_ne
  have h_pos : 0 < rhoPlus c r := Nat.pos_of_ne_zero h_ne
  have : 0 < min (rhoPlus c r) (rhoMinus c r) := lt_min h_pos h
  omega

/-- Contrapositive form: at least one of the two proximities vanishes. -/
theorem rhoPlus_zero_or_rhoMinus_zero (c r : Nat) :
    rhoPlus c r = 0 ∨ rhoMinus c r = 0 := by
  have h_sep := rho_plus_rho_minus_separation c r
  by_cases h : rhoPlus c r = 0
  · exact Or.inl h
  · right
    apply rhoMinus_eq_zero_of_rhoPlus_pos
    exact Nat.pos_of_ne_zero h

/-! ### Monotonicity of the capped 3-adic valuation and proximities

Building blocks for the S214 analytic potential. The capped valuation
`nu3` is monotone in its cap and grows by at most one per step, hence
so do `ρ_+`, `ρ_-`, and `δ_+`. -/

/-- Equation lemma for `nu3` on a positive cap (definitional). -/
private theorem nu3_succ_eq (n c : Nat) :
    nu3 n (c + 1) = (if n = 0 then 0
                     else if n % 3 = 0 then 1 + nu3 (n / 3) c else 0) := rfl

/-- **`nu3` is monotone in the cap**: `nu3 n c ≤ nu3 n (c+1)`. -/
theorem nu3_mono_cap (n c : Nat) : nu3 n c ≤ nu3 n (c+1) := by
  induction c generalizing n with
  | zero => exact Nat.zero_le _
  | succ c ih =>
      by_cases hn : n = 0
      · have h_c1 : nu3 n (c + 1) = 0 := by
          show (if n = 0 then 0 else _) = 0
          rw [if_pos hn]
        have h_c2 : nu3 n (c + 2) = 0 := by
          show (if n = 0 then 0 else _) = 0
          rw [if_pos hn]
        rw [h_c1, h_c2]
      by_cases h3 : n % 3 = 0
      · have h_c1 : nu3 n (c + 1) = 1 + nu3 (n / 3) c := by
          show (if n = 0 then 0
                else if n % 3 = 0 then 1 + nu3 (n / 3) c else 0) = _
          rw [if_neg hn, if_pos h3]
        have h_c2 : nu3 n (c + 2) = 1 + nu3 (n / 3) (c + 1) := by
          show (if n = 0 then 0
                else if n % 3 = 0 then 1 + nu3 (n / 3) (c + 1) else 0) = _
          rw [if_neg hn, if_pos h3]
        rw [h_c1, h_c2]
        exact Nat.add_le_add_left (ih (n / 3)) 1
      · have h_c1 : nu3 n (c + 1) = 0 := by
          show (if n = 0 then 0
                else if n % 3 = 0 then _ else 0) = 0
          rw [if_neg hn, if_neg h3]
        rw [h_c1]
        exact Nat.zero_le _

/-- **`nu3` step bound**: `nu3 n (c+1) ≤ nu3 n c + 1`. -/
theorem nu3_succ_le_succ (n c : Nat) : nu3 n (c+1) ≤ nu3 n c + 1 := by
  induction c generalizing n with
  | zero =>
      have h_n0 : nu3 n 0 = 0 := rfl
      rw [h_n0]
      by_cases hn : n = 0
      · have : nu3 n 1 = 0 := by
          show (if n = 0 then 0 else _) = 0
          rw [if_pos hn]
        rw [this]; omega
      by_cases h3 : n % 3 = 0
      · have : nu3 n 1 = 1 + nu3 (n / 3) 0 := by
          show (if n = 0 then 0
                else if n % 3 = 0 then 1 + nu3 (n / 3) 0 else 0) = _
          rw [if_neg hn, if_pos h3]
        have h_zero : nu3 (n / 3) 0 = 0 := rfl
        rw [this, h_zero]
      · have : nu3 n 1 = 0 := by
          show (if n = 0 then 0
                else if n % 3 = 0 then _ else 0) = 0
          rw [if_neg hn, if_neg h3]
        rw [this]; omega
  | succ c ih =>
      by_cases hn : n = 0
      · have h_c1 : nu3 n (c + 1) = 0 := by
          show (if n = 0 then 0 else _) = 0
          rw [if_pos hn]
        have h_c2 : nu3 n (c + 2) = 0 := by
          show (if n = 0 then 0 else _) = 0
          rw [if_pos hn]
        rw [h_c1, h_c2]; omega
      by_cases h3 : n % 3 = 0
      · have h_c1 : nu3 n (c + 1) = 1 + nu3 (n / 3) c := by
          show (if n = 0 then 0
                else if n % 3 = 0 then 1 + nu3 (n / 3) c else 0) = _
          rw [if_neg hn, if_pos h3]
        have h_c2 : nu3 n (c + 2) = 1 + nu3 (n / 3) (c + 1) := by
          show (if n = 0 then 0
                else if n % 3 = 0 then 1 + nu3 (n / 3) (c + 1) else 0) = _
          rw [if_neg hn, if_pos h3]
        rw [h_c1, h_c2]
        have := ih (n / 3)
        omega
      · have h_c2 : nu3 n (c + 2) = 0 := by
          show (if n = 0 then 0
                else if n % 3 = 0 then _ else 0) = 0
          rw [if_neg hn, if_neg h3]
        rw [h_c2]
        omega

/-- **`ρ_+` monotonicity in `r`**: `ρ_+(c, r) ≤ ρ_+(c, r+1)`. -/
theorem rhoPlus_mono_r (c r : Nat) : rhoPlus c r ≤ rhoPlus c (r+1) := by
  unfold rhoPlus
  by_cases hc : c = 1
  · simp [hc]
  · simp [hc]
    exact nu3_mono_cap (c - 1) r

/-- **`ρ_+` step bound**: `ρ_+(c, r+1) ≤ ρ_+(c, r) + 1`. -/
theorem rhoPlus_succ_le_succ (c r : Nat) : rhoPlus c (r+1) ≤ rhoPlus c r + 1 := by
  unfold rhoPlus
  by_cases hc : c = 1
  · simp [hc]
  · simp [hc]
    exact nu3_succ_le_succ (c - 1) r

/-- **`ρ_-` monotonicity in `r`**: `ρ_-(c, r) ≤ ρ_-(c, r+1)`. -/
theorem rhoMinus_mono_r (c r : Nat) : rhoMinus c r ≤ rhoMinus c (r+1) := by
  unfold rhoMinus
  exact nu3_mono_cap (c + 1) r

/-- **`ρ_-` step bound**: `ρ_-(c, r+1) ≤ ρ_-(c, r) + 1`. -/
theorem rhoMinus_succ_le_succ (c r : Nat) : rhoMinus c (r+1) ≤ rhoMinus c r + 1 := by
  unfold rhoMinus
  exact nu3_succ_le_succ (c + 1) r

/-- **`δ_+` is bounded by the cap**: `ρ_+(c, r) ≤ r`. -/
theorem rhoPlus_le_r (c r : Nat) : rhoPlus c r ≤ r := by
  unfold rhoPlus
  by_cases hc : c = 1
  · simp [hc]
  · simp [hc]
    exact nu3_le_cap (c - 1) r

/-- **`δ_+` monotonicity in `r`**: as the cap grows, the 3-adic
distance from the root weakly grows: `δ_+(c, r) ≤ δ_+(c, r+1)`.

Together with the step bound below, `δ_+(c, r+1) - δ_+(c, r) ∈ {0, 1}`. -/
theorem deltaPlus_mono_r (c r : Nat) : deltaPlus c r ≤ deltaPlus c (r+1) := by
  unfold deltaPlus
  have h_step := rhoPlus_succ_le_succ c r
  have h_bound_r := rhoPlus_le_r c r
  have h_bound_r1 := rhoPlus_le_r c (r + 1)
  omega

/-- **`δ_+` step bound**: `δ_+(c, r+1) ≤ δ_+(c, r) + 1`. Combined with
monotonicity, the increment is exactly `0` or `1` per cap step. -/
theorem deltaPlus_succ_le_succ (c r : Nat) :
    deltaPlus c (r+1) ≤ deltaPlus c r + 1 := by
  unfold deltaPlus
  have h_mono := rhoPlus_mono_r c r
  have h_bound_r := rhoPlus_le_r c r
  have h_bound_r1 := rhoPlus_le_r c (r + 1)
  omega

/-! ### Saturated valuation and goal vertex characterisation -/

/-- **Saturated capped valuation**: if `3^c ∣ n` and `n ≠ 0`, then
`nu3 n c = c`. The capped 3-valuation is fully consumed when `n` has
enough 3-power divisibility. -/
theorem nu3_eq_cap_of_dvd (c : Nat) :
    ∀ (n : Nat), n ≠ 0 → 3 ^ c ∣ n → nu3 n c = c := by
  induction c with
  | zero => intro n _ _; rfl
  | succ c ih =>
      intro n hn h
      have h_div3 : (3 : Nat) ∣ n :=
        dvd_trans (dvd_pow_self 3 (Nat.succ_ne_zero c)) h
      obtain ⟨m, hm⟩ := h_div3
      have h_n_mod : n % 3 = 0 := by
        rw [hm]; exact Nat.mul_mod_right 3 m
      have h_n_div : n / 3 = m := by
        rw [hm]; exact Nat.mul_div_cancel_left _ (by decide : 0 < 3)
      have h_dvd_m : 3 ^ c ∣ m := by
        have h_pow : 3 * 3 ^ c ∣ 3 * m := by
          have h' : 3 ^ (c + 1) ∣ 3 * m := hm ▸ h
          rw [pow_succ, mul_comm (3 ^ c) 3] at h'
          exact h'
        exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp h_pow
      have hm_ne : m ≠ 0 := by
        intro h_eq
        rw [h_eq, Nat.mul_zero] at hm
        exact hn hm
      have h_ih : nu3 m c = c := ih m hm_ne h_dvd_m
      show (if n = 0 then 0
            else if n % 3 = 0 then 1 + nu3 (n / 3) c else 0) = c + 1
      rw [if_neg hn, if_pos h_n_mod, h_n_div, h_ih]
      omega

/-- Goal vertex satisfies `v.c % 3^(R+v.j) = 1` (the standard form,
since `1 < 3^(R+v.j)` whenever `R ≥ 1`). -/
private lemma goal_mod_one (R : Nat) (v : InvVertex) (hR : 1 ≤ R)
    (h : InvVertex.IsGoal v R) : v.c % (3 ^ (R + v.j)) = 1 := by
  unfold InvVertex.IsGoal at h
  have h_pow_ge : 3 ^ (R + v.j) ≥ 3 :=
    calc 3 ^ (R + v.j) ≥ 3 ^ 1 :=
          Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ R + v.j)
      _ = 3 := pow_one 3
  have h_one_mod : 1 % (3 ^ (R + v.j)) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h_one_mod] at h
  exact h

/-- **Goal vanishing of `δ_+`**: at any goal vertex `v` (cylinder
contains the root `1`), the root-distance potential vanishes:
`δ_+(v.c, R + v.j) = 0`.

Foundational for analytic potentials: any candidate `Φ` containing a
positive multiple of `δ_+` automatically has `Φ(goal) = (rest)` with
no `δ_+`-contribution at goals. -/
theorem goal_deltaPlus_zero {R : Nat} (hR : 1 ≤ R) {v : InvVertex}
    (h : InvVertex.IsGoal v R) :
    deltaPlus v.c (R + v.j) = 0 := by
  have h_mod := goal_mod_one R v hR h
  -- Need: rhoPlus v.c (R + v.j) = R + v.j, i.e. nu3 (v.c - 1) (R+v.j) = R+v.j (or vc = 1).
  unfold deltaPlus rhoPlus
  by_cases hc : v.c = 1
  · simp [hc]
  -- v.c ≠ 1; from v.c % m = 1 and m > 1 we get v.c ≥ 1 and dvd.
  have h_m_gt : 1 < 3 ^ (R + v.j) := by
    have : 3 ^ (R + v.j) ≥ 3 := by
      calc 3 ^ (R + v.j) ≥ 3 ^ 1 :=
              Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ R + v.j)
        _ = 3 := pow_one 3
    omega
  have h_vc_ge : v.c ≥ 1 := by
    by_contra h_lt
    have hvc0 : v.c = 0 := by omega
    rw [hvc0] at h_mod
    simp at h_mod
  have h_vc_ge_2 : v.c ≥ 2 := by omega
  have h_vc_sub_ne : v.c - 1 ≠ 0 := by omega
  have h_dvd : (3 : Nat) ^ (R + v.j) ∣ (v.c - 1) := by
    have h_eq : (v.c - 1) % (3 ^ (R + v.j)) = 0 := by
      have hvc_eq : v.c = (v.c - 1) + 1 := by omega
      have : ((v.c - 1) + 1) % (3 ^ (R + v.j)) = 1 := hvc_eq ▸ h_mod
      have h_lt_m : (v.c - 1) % (3 ^ (R + v.j)) < 3 ^ (R + v.j) :=
        Nat.mod_lt _ (by positivity)
      have h_add : ((v.c - 1) % (3 ^ (R + v.j)) + 1 % (3 ^ (R + v.j))) %
                    (3 ^ (R + v.j)) = 1 := by
        rw [← Nat.add_mod]; exact this
      rw [Nat.mod_eq_of_lt h_m_gt] at h_add
      by_cases h_sm : (v.c - 1) % (3 ^ (R + v.j)) + 1 < 3 ^ (R + v.j)
      · rw [Nat.mod_eq_of_lt h_sm] at h_add; omega
      · have h_eq_m : (v.c - 1) % (3 ^ (R + v.j)) + 1 = 3 ^ (R + v.j) := by omega
        rw [h_eq_m, Nat.mod_self] at h_add
        omega
    exact Nat.dvd_of_mod_eq_zero h_eq
  rw [if_neg hc, nu3_eq_cap_of_dvd (R + v.j) (v.c - 1) h_vc_sub_ne h_dvd]
  omega

/-- **Goal vanishing of `ρ_-`**: at any goal vertex, `ρ_-(v.c, R + v.j) = 0`.
Reason: `v.c ≡ 1 (mod 3)` so `v.c + 1 ≡ 2 (mod 3)` is not divisible by `3`. -/
theorem goal_rhoMinus_zero {R : Nat} (hR : 1 ≤ R) {v : InvVertex}
    (h : InvVertex.IsGoal v R) :
    rhoMinus v.c (R + v.j) = 0 := by
  have h_mod := goal_mod_one R v hR h
  have h_vc_mod3 : v.c % 3 = 1 := by
    have h_dvd : (3 : Nat) ∣ 3 ^ (R + v.j) :=
      dvd_pow_self 3 (by omega : R + v.j ≠ 0)
    have hh := (Nat.mod_mod_of_dvd v.c h_dvd).symm
    rw [h_mod] at hh
    omega
  unfold rhoMinus
  apply nu3_eq_zero_of_mod_three_ne_zero
  omega

end CollatzLean4.Admissible
