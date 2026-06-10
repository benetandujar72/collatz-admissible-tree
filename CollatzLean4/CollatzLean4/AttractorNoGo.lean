/-
S242 — The two attractor identities and the no-go for real-valued decaying-modulus
correctors (closing the Iwasawa-collapse loophole at ℝ codomain).

The S242 computational gates (tools/phi_realkam_lp.py, tools/sturmian_gate.py) refuted
both remaining route-B hopes at scale, and isolated the structural cause in two
ONE-LINE identities, formalized here:

  * **the +1 attractor** (τ=2 zero-edge `4y = 3c+1`): `4(y−1) = 3(c−1)`, so
    `ν₃(y−1) = ν₃(c−1) + 1` — a κ-cost-0 edge that gains one 3-adic digit of proximity
    to the goal per step, class-1-self-sustaining;
  * **the −1 attractor** (τ=1 zero-edge `2y = 3c+1`): `2(y+1) = 3(c+1)`, so
    `ν₃(y+1) = ν₃(c+1) + 1` — the κ = −1 filament (class 8 self-sustaining) that makes
    `min-κ(j) = −j` with floor width 1 (the Sturmian/Beatty reduction is dead: optimal
    in-slice paths are the period-1 word `1^∞`, not a log₂3-mechanical word).

With `ν₃(aS202 − 1) = 22` (exact: `aS202 = 1 + 3²²`), the +1 attractor chain gives the
**no-go theorem** `no_decaying_modulus_corrector`: any real-valued Φ satisfying the
κ-edge inequality, the goal bound, the start bound `Φ(start) ≥ m`, AND a 3-adic
continuity modulus (`v.c ≡ w.c mod 3^t` at equal `j` ⟹ `Φv − Φw ≤ ω t`) forces
`m ≤ ω(22 + Q)`: the modulus CANNOT decay — uniformly in `m` and `Q`.  Together with
the ℤ-codomain Iwasawa collapse (S241) this closes the continuity loophole entirely:
no 3-adically-continuous potential of ANY codomain certifies the barrier.  The
surviving corner (hybrid Green-singular + Hölder remainder) is recorded in the gate
tools.

Axioms target: {propext, Classical.choice, Quot.sound}.  Builds narrow.
-/

import CollatzLean4.BitlenPotential
import CollatzLean4.AS202Lift
import CollatzLean4.LadderExists

namespace CollatzLean4.Admissible

/-! ### The two attractor identities (integer level) -/

/-- **The +1 attractor identity**: a τ=2 inverse zero-step `4y = 3c+1` satisfies
`4(y−1) = 3(c−1)`. -/
theorem tau2_attractor {c y : ℕ} (h : 4 * y = 3 * c + 1) :
    4 * (y - 1) = 3 * (c - 1) := by omega

/-- **The −1 attractor identity**: a τ=1 inverse zero-step `2y = 3c+1` satisfies
`2(y+1) = 3(c+1)`. -/
theorem tau1_attractor {c y : ℕ} (h : 2 * y = 3 * c + 1) :
    2 * (y + 1) = 3 * (c + 1) := by omega

/-- The +1 attractor in valuation form: `ν₃(y−1) = ν₃(c−1) + 1` (for `c > 1`). -/
theorem tau2_attractor_nu3 {c y : ℕ} (h : 4 * y = 3 * c + 1) (hc : 1 < c) :
    padicValNat 3 (y - 1) = padicValNat 3 (c - 1) + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hid := tau2_attractor h
  have hc1 : c - 1 ≠ 0 := by omega
  have hy1 : y - 1 ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hid
    omega
  have e1 : padicValNat 3 (4 * (y - 1)) = padicValNat 3 (y - 1) := by
    rw [padicValNat.mul (by norm_num) hy1,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    omega
  have e2 : padicValNat 3 (3 * (c - 1)) = padicValNat 3 (c - 1) + 1 := by
    rw [padicValNat.mul (by norm_num) hc1, padicValNat.self (by norm_num)]
    omega
  rw [← e1, hid, e2]

/-- The −1 attractor in valuation form: `ν₃(y+1) = ν₃(c+1) + 1` (unconditional). -/
theorem tau1_attractor_nu3 {c y : ℕ} (h : 2 * y = 3 * c + 1) :
    padicValNat 3 (y + 1) = padicValNat 3 (c + 1) + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hid := tau1_attractor h
  have e1 : padicValNat 3 (2 * (y + 1)) = padicValNat 3 (y + 1) := by
    rw [padicValNat.mul (by norm_num) (by omega),
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    omega
  have e2 : padicValNat 3 (3 * (c + 1)) = padicValNat 3 (c + 1) + 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
    omega
  rw [← e1, hid, e2]

/-- `ν₃(aS202 − 1) = 22` exactly (`aS202 = 1 + 3²²`): the start sits at 3-adic
distance exactly `3^{−22}` from the goal value `1` — uniformly in `m`. -/
theorem nu3_aS202_sub_one : padicValNat 3 (aS202 - 1) = 22 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h : aS202 - 1 = 3 ^ 22 := by
    rw [aS202_decomp]
    omega
  rw [h]
  exact padicValNat.prime_pow 22

/-! ### The attractor chain (κ-cost-0 goal-shadowing) -/

/-- **The attractor chain.**  For any real-valued `Φ` satisfying the κ-edge inequality,
the τ=2/class-1 attractor chain from `InvStart m` produces, at every depth `q`, a vertex
at level `j = q`, within `3^{−(22+q)}` of the goal value `1`, with `Φ` not below
`Φ(InvStart m)` (each chain edge has κ = 0). -/
theorem attractor_chain (m Q : ℕ) (hm : 1 ≤ m) (Φ : InvVertex → ℝ)
    (hE : ∀ v v' (κ : Int), InvKappaPreciseEdge (22 * m + 2) v v' κ →
      Φ v ≤ (κ : ℝ) + Φ v') :
    ∀ q, q ≤ Q → ∃ v : InvVertex, v.j = q ∧
      v.c % 3 ^ (22 + q) = 1 % 3 ^ (22 + q) ∧ Φ (InvStart m) ≤ Φ v := by
  intro q
  induction q with
  | zero =>
      intro _
      refine ⟨InvStart m, rfl, ?_, le_refl _⟩
      -- (aS202 % 3^(22m+2)) ≡ aS202 ≡ 1 (mod 3^22)
      show aS202 % 3 ^ (22 * m + 2) % 3 ^ (22 + 0) = 1 % 3 ^ (22 + 0)
      have hd : (3 : ℕ) ^ (22 + 0) ∣ 3 ^ (22 * m + 2) := pow_dvd_pow 3 (by omega)
      rw [Nat.mod_mod_of_dvd _ hd]
      have : aS202 ≡ 1 [MOD 3 ^ (22 + 0)] := by
        show _ % _ = _ % _
        rw [aS202_decomp]
        have h22 : (3 : ℕ) ^ (22 + 0) ∣ 3 ^ 22 := by
          rw [Nat.add_zero]
        omega
      exact this
  | succ q ih =>
      intro hqQ
      obtain ⟨v, hj, hcong, hΦ⟩ := ih (by omega)
      -- the constructed τ=2 zero-edge target
      set M1 : ℕ := 3 ^ (22 * m + 2 + v.j + 1) with hM1
      set w : ℕ := invMod2Pow 2 M1 * (3 * v.c + 1) % M1 with hw
      -- cancel: 2^2 · w ≡ 3c+1 (mod M₁)
      have hMge : (3 : ℕ) ≤ M1 := by
        rw [hM1]
        calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ (22 * m + 2 + v.j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcancel : (2 ^ 2 * invMod2Pow 2 M1) % M1 = 1 := by
        rw [hM1]
        exact invMod2Pow_cancel 2 (22 * m + 2 + v.j + 1) (by omega)
      have hcanc' : 2 ^ 2 * invMod2Pow 2 M1 ≡ 1 [MOD M1] := by
        show _ % _ = _ % _
        rw [hcancel, Nat.mod_eq_of_lt (by omega)]
      have hK1 : 2 ^ 2 * w ≡ 3 * v.c + 1 [MOD M1] := by
        rw [hw]
        calc 2 ^ 2 * (invMod2Pow 2 M1 * (3 * v.c + 1) % M1)
            ≡ 2 ^ 2 * (invMod2Pow 2 M1 * (3 * v.c + 1)) [MOD M1] :=
              (Nat.mod_modEq _ _).mul_left _
          _ = (2 ^ 2 * invMod2Pow 2 M1) * (3 * v.c + 1) := by ring
          _ ≡ 1 * (3 * v.c + 1) [MOD M1] := hcanc'.mul_right _
          _ = 3 * v.c + 1 := by ring
      -- the target is ≡ 1 mod 3^(22+q+1): the +1 attractor at residue level
      have hdvd1 : (3 : ℕ) ^ (22 + q + 1) ∣ M1 := by
        rw [hM1]
        exact pow_dvd_pow 3 (by omega)
      have hstep1 : 3 * v.c + 1 ≡ 4 [MOD 3 ^ (22 + q + 1)] := by
        have h3 : 3 * v.c ≡ 3 * 1 [MOD 3 * 3 ^ (22 + q)] := by
          show _ % _ = _ % _
          rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hcong]
        have h3L : 3 * 3 ^ (22 + q) = 3 ^ (22 + q + 1) := by rw [pow_succ]; ring
        rw [h3L] at h3
        have := h3.add_right 1
        simpa using this
      have hw1 : 2 ^ 2 * w ≡ 2 ^ 2 * 1 [MOD 3 ^ (22 + q + 1)] := by
        calc 2 ^ 2 * w ≡ 3 * v.c + 1 [MOD 3 ^ (22 + q + 1)] := hK1.of_dvd hdvd1
          _ ≡ 4 [MOD 3 ^ (22 + q + 1)] := hstep1
          _ = 2 ^ 2 * 1 := by norm_num
      have hcop : Nat.Coprime (3 ^ (22 + q + 1)) (2 ^ 2) := by
        apply Nat.Coprime.pow
        decide
      have hwcong : w ≡ 1 [MOD 3 ^ (22 + q + 1)] :=
        Nat.ModEq.cancel_left_of_coprime hcop hw1
      -- class data: w ≡ 1 (mod 9) ⟹ tau w = 2, InX w
      have hw9 : w % 9 = 1 := by
        have h9d : (9 : ℕ) ∣ 3 ^ (22 + q + 1) := by
          rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]
          exact pow_dvd_pow 3 (by omega)
        have h := hwcong.of_dvd h9d
        have h19 : (1 : ℕ) % 9 = 1 := by norm_num
        rw [Nat.ModEq, h19] at h
        exact h
      have htauw : tau w = 2 := by
        simp only [tau, hw9]
      have hXw : InX w := by
        unfold InX
        omega
      -- the zero-edge and its κ = 0 disjunct
      have hedge : InvEdgeZero (22 * m + 2) v ⟨v.j + 1, w⟩ ((tau w : Int) - 2) := by
        refine ⟨rfl, hXw, ?_, rfl⟩
        show (3 * v.c + 1) % 3 ^ (22 * m + 2 + (v.j + 1))
            = (2 ^ tau w * w) % 3 ^ (22 * m + 2 + (v.j + 1))
        rw [htauw]
        exact hK1.symm
      have hκ : InvKappaPreciseEdge (22 * m + 2) v ⟨v.j + 1, w⟩ 0 :=
        Or.inr (Or.inr (⟨(tau w : Int) - 2, hedge, le_of_eq htauw.symm, rfl⟩))
      have hΦstep := hE v ⟨v.j + 1, w⟩ 0 hκ
      refine ⟨⟨v.j + 1, w⟩, by simp [hj], ?_, ?_⟩
      · show w % 3 ^ (22 + (q + 1)) = 1 % 3 ^ (22 + (q + 1))
        have : (22 + (q + 1)) = (22 + q + 1) := by omega
        rw [this]
        exact hwcong
      · calc Φ (InvStart m) ≤ Φ v := hΦ
          _ ≤ (0 : ℝ) + Φ ⟨v.j + 1, w⟩ := by
              simpa using hΦstep
          _ = Φ ⟨v.j + 1, w⟩ := by ring

/-! ### The no-go theorem -/

/-- **No real-valued decaying-modulus corrector (S242).**  Any `Φ : InvVertex → ℝ`
satisfying the κ-edge inequality, the goal bound on the `Q`-slice, the start bound
`Φ(InvStart m) ≥ m`, and a 3-adic continuity modulus `ω` (equal `j`, `c ≡ c' mod 3^t`
⟹ `Φv − Φv' ≤ ω t`) forces `m ≤ ω(22 + Q)`: the modulus cannot decay below `m` at
depth `22 + Q` — uniformly in `m` and `Q`.  With the ℤ-codomain collapse this closes
the 3-adic-continuity loophole for route-B potentials at every codomain. -/
theorem no_decaying_modulus_corrector (m Q : ℕ) (hm : 1 ≤ m)
    (Φ : InvVertex → ℝ) (ω : ℕ → ℝ)
    (hE : ∀ v v' (κ : Int), InvKappaPreciseEdge (22 * m + 2) v v' κ →
      Φ v ≤ (κ : ℝ) + Φ v')
    (hG : ∀ v : InvVertex, InvVertex.IsGoal v (22 * m + 2) → v.j ≤ Q → Φ v ≤ 0)
    (hS : (m : ℝ) ≤ Φ (InvStart m))
    (hH : ∀ v w : InvVertex, ∀ t : ℕ, v.j = w.j →
      v.c % 3 ^ t = w.c % 3 ^ t → Φ v - Φ w ≤ ω t) :
    (m : ℝ) ≤ ω (22 + Q) := by
  obtain ⟨v, hj, hcong, hΦ⟩ := attractor_chain m Q hm Φ hE Q (le_refl Q)
  -- the goal vertex at the same level
  have hgoal : InvVertex.IsGoal ⟨Q, 1⟩ (22 * m + 2) := rfl
  have hΦgoal : Φ ⟨Q, 1⟩ ≤ 0 := hG ⟨Q, 1⟩ hgoal (le_refl Q)
  -- the Hölder hop at depth 22 + Q
  have hhop : Φ v - Φ ⟨Q, 1⟩ ≤ ω (22 + Q) := by
    apply hH v ⟨Q, 1⟩ (22 + Q) (by simpa using hj)
    simpa using hcong
  calc (m : ℝ) ≤ Φ (InvStart m) := hS
    _ ≤ Φ v := hΦ
    _ = (Φ v - Φ ⟨Q, 1⟩) + Φ ⟨Q, 1⟩ := by ring
    _ ≤ ω (22 + Q) + 0 := add_le_add hhop hΦgoal
    _ = ω (22 + Q) := by ring

end CollatzLean4.Admissible
