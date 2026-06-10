/-
S240 — T3: every unit cylinder is reachable (`Reach = units`, at every precision).

The internal prize identified by the S240 p-adic-orbit scoping: formalize the
self-sustaining induction of `tools/b1_reach_is_units.py` / `b1_surjectivity.py`.

**Theorem** (`invReachable_units`): for every `t ≥ 1` and every `z` coprime to `3`, some
vertex reachable from `InvStart m` has `c ≡ z (mod 3^t)`.  Consequences:
  * the "piece C" of the program (general-cylinder reachability, unbounded `j`) closes
    POSITIVELY — every unit cylinder, including the deep-jump trap `c ≡ 4`
    (`invReachable_hits_trap`), is reachable at every precision;
  * invariant-nonexistence becomes a THEOREM: no congruence invariant at any finite
    modulus separates the start from any unit cylinder (they are all reachable).

**The key structural discovery** that makes the induction a one-zero-edge-per-level
affair: for EVERY admissible class `α = z mod 9 ∈ X`, the value `2^{τ(α)}·α mod 9` lands
in `{4, 7}` (`two_pow_tau_mul_mod9`; the six cases are `4·1=4`, `2·2=4`, `4·4≡7`,
`8·5≡4`, `16·7≡4`, `2·8≡7`).  Hence every unit `z` is the DIRECT image of one zero-edge:
`z ≡ 2^{-τ(z)}·(3u+1)` with `u := (2^{τ(z)}·z − 1)/3` again a unit.  Since multiplication
by 3 gains one digit (`c ≡ u mod 3^L ⟹ 3c+1 ≡ 3u+1 mod 3^(L+1)`), matching `u` to
precision `L` pins the zero-edge target to precision `L+1`: the induction gains exactly
one digit per zero-edge from the trivial precision-1 base.

No native_decide; reuses `invMod2Pow_cancel` (LadderExists) and the DlogReachable
reachability API.  Builds narrow.
-/

import CollatzLean4.DlogReachable
import CollatzLean4.LadderExists

namespace CollatzLean4.Admissible

/-! ### The mod-9 table: `2^{τ(α)}·α ∈ {4,7} (mod 9)` for every admissible class -/

/-- For every `z` coprime to `3`, the value `2^{τ(z)}·z` is `≡ 4` or `7 (mod 9)` —
equivalently, `(2^{τ(z)}·z − 1)/3` is again a unit. -/
theorem two_pow_tau_mul_mod9 (z : ℕ) (hz : z % 3 ≠ 0) :
    (2 ^ tau z * z) % 9 = 4 ∨ (2 ^ tau z * z) % 9 = 7 := by
  have h93 : z % 9 % 3 = z % 3 := Nat.mod_mod_of_dvd z (by norm_num)
  have hz9 : z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 7 ∨ z % 9 = 8 := by
    omega
  rw [Nat.mul_mod]
  rcases hz9 with h | h | h | h | h | h <;> simp only [tau, h] <;> decide

/-- The unit-lift arithmetic: `u := (2^{τ(z)}·z − 1)/3` satisfies `3u + 1 = 2^{τ(z)}·z`
and is itself coprime to `3`. -/
theorem tau_lift_unit (z : ℕ) (hz : z % 3 ≠ 0) :
    3 * ((2 ^ tau z * z - 1) / 3) + 1 = 2 ^ tau z * z ∧
      ((2 ^ tau z * z - 1) / 3) % 3 ≠ 0 := by
  have hy9 := two_pow_tau_mul_mod9 z hz
  have h93 : (2 ^ tau z * z) % 9 % 3 = (2 ^ tau z * z) % 3 :=
    Nat.mod_mod_of_dvd _ (by norm_num)
  have hdvd : 3 ∣ 2 ^ tau z * z - 1 := by omega
  have hmul := Nat.mul_div_cancel' hdvd
  constructor
  · omega
  · have h39 : (3 * ((2 ^ tau z * z - 1) / 3)) % 9
        = 3 * (((2 ^ tau z * z - 1) / 3) % 3) := by
      rw [show (9 : ℕ) = 3 * 3 from rfl, Nat.mul_mod_mul_left]
    omega

/-! ### The zero-edge lift (the workhorse: one digit of precision per zero-edge) -/

/-- **Zero-edge lift.**  From a reachable vertex `v` matching `u := (2^{τ(z)}·z − 1)/3`
to precision `3^L` (`1 ≤ L ≤` v's level), one zero-edge reaches a vertex matching `z`
to precision `3^(L+1)`. -/
theorem invReachable_zero_lift (m : ℕ) {v : InvVertex} (hv : InvReachable m v)
    (L : ℕ) (hL : 1 ≤ L) (hlev : L ≤ 22 * m + 2 + v.j)
    (z : ℕ) (hz3 : z % 3 ≠ 0)
    (hcong : v.c % 3 ^ L = ((2 ^ tau z * z - 1) / 3) % 3 ^ L) :
    ∃ v' : InvVertex, InvReachable m v' ∧ v'.j = v.j + 1 ∧
      v'.c % 3 ^ (L + 1) = z % 3 ^ (L + 1) := by
  obtain ⟨h3u, _⟩ := tau_lift_unit z hz3
  set w : ℕ := invMod2Pow (tau z) (3 ^ (22 * m + 2 + v.j + 1)) * (3 * v.c + 1)
      % 3 ^ (22 * m + 2 + v.j + 1) with hwdef
  have hMge : (3 : ℕ) ≤ 3 ^ (22 * m + 2 + v.j + 1) := by
    calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ (22 * m + 2 + v.j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcancel : (2 ^ tau z * invMod2Pow (tau z) (3 ^ (22 * m + 2 + v.j + 1)))
      % 3 ^ (22 * m + 2 + v.j + 1) = 1 :=
    invMod2Pow_cancel (tau z) (22 * m + 2 + v.j + 1) (by omega)
  have hcanc' : 2 ^ tau z * invMod2Pow (tau z) (3 ^ (22 * m + 2 + v.j + 1))
      ≡ 1 [MOD 3 ^ (22 * m + 2 + v.j + 1)] := by
    show _ % _ = _ % _
    rw [hcancel, Nat.mod_eq_of_lt (by omega)]
  -- K1: the cancel congruence at the working level
  have hK1 : 2 ^ tau z * w ≡ 3 * v.c + 1 [MOD 3 ^ (22 * m + 2 + v.j + 1)] := by
    rw [hwdef]
    calc 2 ^ tau z * (invMod2Pow (tau z) (3 ^ (22 * m + 2 + v.j + 1)) * (3 * v.c + 1)
          % 3 ^ (22 * m + 2 + v.j + 1))
        ≡ 2 ^ tau z * (invMod2Pow (tau z) (3 ^ (22 * m + 2 + v.j + 1)) * (3 * v.c + 1))
            [MOD 3 ^ (22 * m + 2 + v.j + 1)] := (Nat.mod_modEq _ _).mul_left _
      _ = (2 ^ tau z * invMod2Pow (tau z) (3 ^ (22 * m + 2 + v.j + 1))) * (3 * v.c + 1) := by
          ring
      _ ≡ 1 * (3 * v.c + 1) [MOD 3 ^ (22 * m + 2 + v.j + 1)] := hcanc'.mul_right _
      _ = 3 * v.c + 1 := by ring
  -- K2: matching u to precision L pins 3c+1 to precision L+1
  have hK2 : 3 * v.c + 1 ≡ 3 * ((2 ^ tau z * z - 1) / 3) + 1 [MOD 3 ^ (L + 1)] := by
    have h2 : 3 * v.c ≡ 3 * ((2 ^ tau z * z - 1) / 3) [MOD 3 * 3 ^ L] := by
      show _ % _ = _ % _
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hcong]
    have h3L : 3 * 3 ^ L = 3 ^ (L + 1) := by rw [pow_succ]; ring
    rw [h3L] at h2
    exact h2.add_right 1
  -- K3/K4: the target matches z to precision L+1
  have hdvdL : (3 : ℕ) ^ (L + 1) ∣ 3 ^ (22 * m + 2 + v.j + 1) :=
    pow_dvd_pow 3 (by omega)
  have hK4 : 2 ^ tau z * w ≡ 2 ^ tau z * z [MOD 3 ^ (L + 1)] := by
    calc 2 ^ tau z * w ≡ 3 * v.c + 1 [MOD 3 ^ (L + 1)] := hK1.of_dvd hdvdL
      _ ≡ 3 * ((2 ^ tau z * z - 1) / 3) + 1 [MOD 3 ^ (L + 1)] := hK2
      _ = 2 ^ tau z * z := h3u
  have hcop : Nat.Coprime (3 ^ (L + 1)) (2 ^ tau z) := by
    apply Nat.Coprime.pow
    decide
  have hK3 : w ≡ z [MOD 3 ^ (L + 1)] :=
    Nat.ModEq.cancel_left_of_coprime hcop hK4
  -- the class data
  have hw9 : w % 9 = z % 9 := by
    have h9d : (9 : ℕ) ∣ 3 ^ (L + 1) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]
      exact pow_dvd_pow 3 (by omega)
    exact hK3.of_dvd h9d
  have hXz : InX z := by
    have h93 : z % 9 % 3 = z % 3 := Nat.mod_mod_of_dvd z (by norm_num)
    unfold InX
    omega
  have hXw : InX w := by
    unfold InX at hXz ⊢
    omega
  have htauw : tau w = tau z := by
    unfold tau
    rw [hw9]
  -- the zero-edge
  have hedge : InvEdgeZero (22 * m + 2) v ⟨v.j + 1, w⟩ ((tau w : Int) - 2) := by
    refine ⟨rfl, hXw, ?_, rfl⟩
    show (3 * v.c + 1) % 3 ^ (22 * m + 2 + (v.j + 1))
        = (2 ^ tau w * w) % 3 ^ (22 * m + 2 + (v.j + 1))
    rw [htauw]
    exact hK1.symm
  exact ⟨⟨v.j + 1, w⟩, invReachable_step m hv (Or.inr hedge), rfl, hK3⟩

/-! ### The main theorem: every unit cylinder is reachable -/

/-- **`Reach = units` (S240, T3).**  For every precision `t ≥ 1` and every `z` coprime
to `3`, some vertex reachable from `InvStart m` matches `z` mod `3^t`.  Closes the
program's "general-cylinder reachability" piece POSITIVELY and turns the nonexistence of
separating congruence invariants (at any finite modulus) into a theorem. -/
theorem invReachable_units (m : ℕ) :
    ∀ t, 1 ≤ t → ∀ z : ℕ, z % 3 ≠ 0 →
      ∃ v : InvVertex, InvReachable m v ∧ t ≤ 22 * m + 2 + v.j ∧
        v.c % 3 ^ t = z % 3 ^ t := by
  intro t
  induction t with
  | zero => intro ht; exact absurd ht (by omega)
  | succ L ih =>
      intro _ z hz3
      have hstart3 : (InvStart m).c % 3 = 1 := by
        show aS202 % 3 ^ (22 * m + 2) % 3 = 1
        have hd : (3 : ℕ) ∣ 3 ^ (22 * m + 2) := dvd_pow_self 3 (by omega)
        rw [Nat.mod_mod_of_dvd _ hd, aS202_decomp]
        have hd22 : (3 : ℕ) ∣ 3 ^ 22 := dvd_pow_self 3 (by norm_num)
        omega
      rcases Nat.eq_zero_or_pos L with rfl | hL
      · -- base t = 1: the two classes mod 3
        have hz : z % 3 = 1 ∨ z % 3 = 2 := by omega
        rcases hz with h1 | h2
        · -- z ≡ 1 (mod 3): the start itself
          refine ⟨InvStart m, invReachable_start m, ?_, ?_⟩
          · have hj0 : (InvStart m).j = 0 := rfl
            omega
          · rw [pow_one, hstart3, h1]
        · -- z ≡ 2 (mod 3): one zero-edge to the lift of z' = 2
          have hcongB : (InvStart m).c % 3 ^ 1 = ((2 ^ tau 2 * 2 - 1) / 3) % 3 ^ 1 := by
            rw [pow_one, hstart3]
            decide
          obtain ⟨v', hv', hj', hc'⟩ :=
            invReachable_zero_lift m (invReachable_start m) 1 (le_refl 1)
              (by have hj0 : (InvStart m).j = 0 := rfl; omega)
              2 (by norm_num) hcongB
          refine ⟨v', hv', by omega, ?_⟩
          have h9 : v'.c % 3 ^ (1 + 1) = 2 % 3 ^ (1 + 1) := hc'
          norm_num at h9
          have h93 : v'.c % 9 % 3 = v'.c % 3 := Nat.mod_mod_of_dvd v'.c (by norm_num)
          rw [pow_one]
          omega
      · -- step t = L + 1, L ≥ 1: lift through one zero-edge
        obtain ⟨h3u, hu3⟩ := tau_lift_unit z hz3
        obtain ⟨v, hv, hlev, hcong⟩ := ih hL ((2 ^ tau z * z - 1) / 3) hu3
        obtain ⟨v', hv', hj', hcong'⟩ :=
          invReachable_zero_lift m hv L hL (by omega) z hz3 hcong
        exact ⟨v', hv', by omega, hcong'⟩

/-- **The trap cylinder is reachable at every precision** — the `dlog = 2 / c ≡ 4`
cylinder (the deep-jump trap of the S240 analysis) contains reachable vertices at
every modulus `3^t`. -/
theorem invReachable_hits_trap (m t : ℕ) (ht : 1 ≤ t) :
    ∃ v : InvVertex, InvReachable m v ∧ v.c % 3 ^ t = 4 % 3 ^ t := by
  obtain ⟨v, hv, _, hc⟩ := invReachable_units m t ht 4 (by norm_num)
  exact ⟨v, hv, hc⟩

end CollatzLean4.Admissible
