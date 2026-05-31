/-
S240 — Phase 1 (full): existence of the trap-reaching ladder, and the negative theorem
`not_firstMPrecisionSuffixPositive`.

The S240 reachability verdict (trap-reachable) refutes the canonical-first-split device.  This
module machine-checks that refutation.  Architecture (per the Plan agent):
  * Lemma 1  `two_pow_mod_nine`        — period-6 of 2^e mod 9.
  * Lemma 2  class/tau from d % 6      — vertex `⟨1, 2^d % 3^K⟩` has class 4 (d≡2) or 7 (d≡4).
  * Lemma 3  `ladder_step_{seven,four}`— the one-edge descent brick (κ=+1), no dlog inside.
  * Lemma 4  `ladder_exists`           — strong induction on d: a one-edge WPath to the trap.
  * Lemma 5  `entry_zeroEdge`          — InvStart(m+1) → s1 (class 7); dlog W as existential bridge.
  * Lemma 6  `not_firstMPrecisionSuffixPositive` — assemble (mid=goal, vs₂=[], κ₂=0).

No new native_decide; aS202's value is never computed.  Builds narrow.
-/

import CollatzLean4.LadderRefutation
import CollatzLean4.S212Forward
import CollatzLean4.DlogReachable
import CollatzLean4.UniformBarrier

namespace CollatzLean4.Admissible

/-! ### Lemma 1 — period-6 of `2^e mod 9` -/

/-- `2^e mod 9` has period 6 (since `ord(2 mod 9) = 6`, `2^6 = 64 ≡ 1`). -/
theorem two_pow_mod_nine (e : ℕ) : 2 ^ e % 9 = 2 ^ (e % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod e 6, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-! ### Lemma 2 — class and `tau` of a ladder vertex from `d % 6` -/

/-- The mod-9 class of `2^d % 3^K` depends only on `d % 6` (for `K ≥ 2`, since `9 ∣ 3^K`). -/
theorem two_pow_mod9_eq (K d : ℕ) (hK : 2 ≤ K) :
    (2 ^ d % 3 ^ K) % 9 = 2 ^ (d % 6) % 9 := by
  have h9 : (9 : ℕ) ∣ 3 ^ K := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]; exact pow_dvd_pow 3 hK
  rw [Nat.mod_mod_of_dvd _ h9, two_pow_mod_nine]

/-- A ladder vertex at `d ≡ 2 (mod 6)` has class `4`. -/
theorem class_four_of_mod6 (K d : ℕ) (hK : 2 ≤ K) (h : d % 6 = 2) :
    (2 ^ d % 3 ^ K) % 9 = 4 := by
  rw [two_pow_mod9_eq K d hK, h]; decide

/-- A ladder vertex at `d ≡ 4 (mod 6)` has class `7`. -/
theorem class_seven_of_mod6 (K d : ℕ) (hK : 2 ≤ K) (h : d % 6 = 4) :
    (2 ^ d % 3 ^ K) % 9 = 7 := by
  rw [two_pow_mod9_eq K d hK, h]; decide

/-- `tau` of a class-4 residue is `2`. -/
theorem tau_class_four (n : ℕ) (h : n % 9 = 4) : tau n = 2 := by
  simp only [tau, h]

/-- `tau` of a class-7 residue is `4`. -/
theorem tau_class_seven (n : ℕ) (h : n % 9 = 7) : tau n = 4 := by
  simp only [tau, h]

/-- A class-4 or class-7 residue is admissible. -/
theorem InX_class_four (n : ℕ) (h : n % 9 = 4) : InX n := by
  unfold InX; omega

theorem InX_class_seven (n : ℕ) (h : n % 9 = 7) : InX n := by
  unfold InX; omega

/-! ### Lemma 3 — the one-edge ladder step (no dlog inside; pure `2^d` arithmetic) -/

/-- The descent one-edge `⟨1, 2^d % M⟩ → ⟨1, 2^(d-τ) % M⟩` (M = 3^(R+1)).  The consistency
`2^d ≡ 2^τ · 2^(d-τ) (mod M)` is `pow_add` (`τ + (d-τ) = d`), no discrete log needed. -/
theorem oneEdge_two_pow (R d τ : ℕ) (hR : 1 ≤ R) (hτd : τ ≤ d)
    (hτ : tau (2 ^ (d - τ) % 3 ^ (R + 1)) = τ)
    (hX : InX (2 ^ (d - τ) % 3 ^ (R + 1))) :
    InvEdgeOne R ⟨1, 2 ^ d % 3 ^ (R + 1)⟩ ⟨1, 2 ^ (d - τ) % 3 ^ (R + 1)⟩ (τ : Int) := by
  refine ⟨rfl, hX, ?_, by rw [hτ]⟩
  show (2 ^ d % 3 ^ (R + 1)) % 3 ^ (R + 1)
      = (2 ^ tau (2 ^ (d - τ) % 3 ^ (R + 1)) * (2 ^ (d - τ) % 3 ^ (R + 1))) % 3 ^ (R + 1)
  rw [hτ, Nat.mod_mod_of_dvd _ (dvd_refl _)]
  have hkey : (2 ^ τ * (2 ^ (d - τ) % 3 ^ (R + 1))) % 3 ^ (R + 1) = 2 ^ d % 3 ^ (R + 1) := by
    have h1 : 2 ^ τ * (2 ^ (d - τ) % 3 ^ (R + 1)) ≡ 2 ^ τ * 2 ^ (d - τ) [MOD 3 ^ (R + 1)] :=
      (Nat.mod_modEq _ _).mul_left _
    have h2 : 2 ^ τ * 2 ^ (d - τ) = 2 ^ d := by rw [← pow_add]; congr 1; omega
    rw [h2] at h1
    exact h1
  rw [hkey]

/-- Ladder step from a class-7 vertex (`d ≡ 4 mod 6`): one-edge of weight `τ = 2` to class 4. -/
theorem ladder_step_seven (R d : ℕ) (hR : 1 ≤ R) (h : d % 6 = 4) (hd : 4 ≤ d) :
    InvKappaPreciseEdge R ⟨1, 2 ^ d % 3 ^ (R + 1)⟩ ⟨1, 2 ^ (d - 2) % 3 ^ (R + 1)⟩ 1 := by
  have hcl : (2 ^ (d - 2) % 3 ^ (R + 1)) % 9 = 4 :=
    class_four_of_mod6 (R + 1) (d - 2) (by omega) (by omega)
  have hτ : tau (2 ^ (d - 2) % 3 ^ (R + 1)) = 2 := tau_class_four _ hcl
  have hX : InX (2 ^ (d - 2) % 3 ^ (R + 1)) := InX_class_four _ hcl
  exact Or.inl ⟨_, oneEdge_two_pow R d 2 hR (by omega) hτ hX, rfl⟩

/-- Ladder step from a class-4 vertex (`d ≡ 2 mod 6`, `d ≥ 8`): one-edge of weight `τ = 4`
to class 7.  (`d ≥ 8` prevents the `d - 4` underflow; `d = 2` is the trap terminus, never a source.) -/
theorem ladder_step_four (R d : ℕ) (hR : 1 ≤ R) (h : d % 6 = 2) (hd : 8 ≤ d) :
    InvKappaPreciseEdge R ⟨1, 2 ^ d % 3 ^ (R + 1)⟩ ⟨1, 2 ^ (d - 4) % 3 ^ (R + 1)⟩ 1 := by
  have hcl : (2 ^ (d - 4) % 3 ^ (R + 1)) % 9 = 7 :=
    class_seven_of_mod6 (R + 1) (d - 4) (by omega) (by omega)
  have hτ : tau (2 ^ (d - 4) % 3 ^ (R + 1)) = 4 := tau_class_seven _ hcl
  have hX : InX (2 ^ (d - 4) % 3 ^ (R + 1)) := InX_class_seven _ hcl
  exact Or.inl ⟨_, oneEdge_two_pow R d 4 hR (by omega) hτ hX, rfl⟩

/-! ### Lemma 5 helpers — the modular inverse of `2^τ` mod `3^k` -/

/-- `2 · invMod2(3^k) ≡ 1 (mod 3^k)`: `invMod2 M = (M+1)/2` is the inverse of 2 for odd `M`. -/
theorem two_mul_invMod2 (k : ℕ) (hk : 1 ≤ k) : (2 * invMod2 (3 ^ k)) % 3 ^ k = 1 := by
  have h1lt : 1 < 3 ^ k := by
    calc (1 : ℕ) < 3 := by norm_num
      _ = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hodd : 3 ^ k % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  have hval : 2 * invMod2 (3 ^ k) = 3 ^ k + 1 := by unfold invMod2; omega
  rw [hval, Nat.add_mod_left, Nat.mod_eq_of_lt h1lt]

/-- `2^τ · invMod2Pow τ (3^k) ≡ 1 (mod 3^k)`. -/
theorem invMod2Pow_cancel (τ k : ℕ) (hk : 1 ≤ k) :
    (2 ^ τ * invMod2Pow τ (3 ^ k)) % 3 ^ k = 1 := by
  have h1lt : 1 < 3 ^ k := by
    calc (1 : ℕ) < 3 := by norm_num
      _ = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hA : (2 * invMod2 (3 ^ k)) % 3 ^ k = 1 := two_mul_invMod2 k hk
  unfold invMod2Pow
  have e1 : (2 ^ τ * (invMod2 (3 ^ k) ^ τ % 3 ^ k)) % 3 ^ k
      = (2 ^ τ * invMod2 (3 ^ k) ^ τ) % 3 ^ k :=
    (Nat.mod_modEq _ _).mul_left _
  rw [e1, ← mul_pow, Nat.pow_mod, hA, one_pow, Nat.mod_eq_of_lt h1lt]

/-- `invMod2Pow 4 (3^k) ≡ 4 (mod 9)` (the inverse of `2^4 ≡ 7 mod 9` is `4`). -/
theorem invMod2Pow_four_mod9 (k : ℕ) (hk : 2 ≤ k) : invMod2Pow 4 (3 ^ k) % 9 = 4 := by
  have hcancel : (2 ^ 4 * invMod2Pow 4 (3 ^ k)) % 3 ^ k = 1 := invMod2Pow_cancel 4 k (by omega)
  have h9 : (9 : ℕ) ∣ 3 ^ k := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]; exact pow_dvd_pow 3 hk
  have h9eq : (2 ^ 4 * invMod2Pow 4 (3 ^ k)) % 9 = 1 := by
    rw [← Nat.mod_mod_of_dvd _ h9, hcancel]
  rw [Nat.mul_mod] at h9eq
  have h16 : (2 : ℕ) ^ 4 % 9 = 7 := by norm_num
  rw [h16] at h9eq
  omega

/-! ### Lemma 4 — existence of the trap-reaching ladder (strong induction on `d`) -/

/-- **The ladder exists.**  From any `⟨1, 2^d % 3^(R+1)⟩` with `d ≡ 2 or 4 (mod 6)` and `d ≥ 2`,
there is a one-edge κ-precise WPath down to the trap `⟨1, 2^2 % 3^(R+1)⟩` (dlog 2, `c = 4`), of
total κ-weight equal to its length, with every interior vertex of class 4 or 7 (hence non-m-precise
by the shield).  The path has length `~(d-2)/3` (astronomical at real scale) but is constructed by
induction on `d`, never enumerated. -/
theorem ladder_exists (R : ℕ) (hR : 1 ≤ R) :
    ∀ d, (d % 6 = 2 ∨ d % 6 = 4) → 2 ≤ d →
    ∃ (vs : List InvVertex) (κ : Int),
      WPath (InvKappaPreciseEdge R) ⟨1, 2 ^ d % 3 ^ (R + 1)⟩ ⟨1, 2 ^ 2 % 3 ^ (R + 1)⟩ κ vs ∧
      κ = (vs.length : Int) ∧
      (∀ x ∈ vs, x.c % 9 = 4 ∨ x.c % 9 = 7) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd6 hd
    by_cases hd2 : d = 2
    · subst hd2
      exact ⟨[], 0, ⟨rfl, rfl⟩, by simp, by simp⟩
    · rcases hd6 with h2 | h4
      · -- d % 6 = 2, d ≠ 2 ⟹ d ≥ 8; step τ = 4 to class 7
        obtain ⟨vs', κ', hpath', hκ', hshield'⟩ :=
          ih (d - 4) (by omega) (Or.inr (by omega)) (by omega)
        refine ⟨⟨1, 2 ^ (d - 4) % 3 ^ (R + 1)⟩ :: vs', 1 + κ', ?_, ?_, ?_⟩
        · exact ⟨1, κ', ladder_step_four R d hR h2 (by omega), hpath', rfl⟩
        · rw [hκ', List.length_cons]; push_cast; ring
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact Or.inr (class_seven_of_mod6 (R + 1) (d - 4) (by omega) (by omega))
          · exact hshield' x hmem
      · -- d % 6 = 4, d ≥ 4; step τ = 2 to class 4
        obtain ⟨vs', κ', hpath', hκ', hshield'⟩ :=
          ih (d - 2) (by omega) (Or.inl (by omega)) (by omega)
        refine ⟨⟨1, 2 ^ (d - 2) % 3 ^ (R + 1)⟩ :: vs', 1 + κ', ?_, ?_, ?_⟩
        · exact ⟨1, κ', ladder_step_seven R d hR h4 (by omega), hpath', rfl⟩
        · rw [hκ', List.length_cons]; push_cast; ring
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact Or.inl (class_four_of_mod6 (R + 1) (d - 2) (by omega) (by omega))
          · exact hshield' x hmem

/-- `2^(e%6) ≡ 7 (mod 9)` forces `e % 6 = 4` (standalone, fresh variable — avoids whnf on the
irreducible `dlog`-derived `W` inside a heavy context). -/
theorem mod6_of_two_pow_mod9_seven (e : ℕ) (h : 2 ^ (e % 6) % 9 = 7) : e % 6 = 4 := by
  have hlt : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize hj : e % 6 = j at h hlt
  interval_cases j <;> revert h <;> decide

/-- A unit `c1 ≡ 7 (mod 9)` (with `c1 < 3^k`, `k ≥ 2`) is `2^W % 3^k` for some `W ≡ 4 (mod 6)`.
The exponent `k` is a BARE variable so `ZMod (3^k)`'s instances do not `whnf` the compound
`22(m+1)+3` exponent (which loops); the caller instantiates `k := 22(m+1)+3`. -/
theorem unit_eq_two_pow_mod9 (k c1 : ℕ) (hk : 2 ≤ k) (hc3 : c1 % 3 = 1)
    (hc1lt : c1 < 3 ^ k) (hc19 : c1 % 9 = 7) :
    ∃ W, c1 = 2 ^ W % 3 ^ k ∧ W % 6 = 4 := by
  have hco : Nat.Coprime c1 3 := by
    have hnd : ¬ (3 ∣ c1) := by intro hd; omega
    exact Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr hnd)
  have hunit : IsUnit ((c1 : ZMod (3 ^ k))) :=
    (ZMod.isUnit_iff_coprime c1 (3 ^ k)).mpr (hco.pow_right _)
  obtain ⟨W, hW⟩ := exists_two_pow_eq_of_isUnit k (by omega) hunit
  have hc1eq : c1 = 2 ^ W % 3 ^ k := by
    have hmod : (2 ^ W : ℕ) % 3 ^ k = c1 % 3 ^ k := by
      have hh : (2 ^ W : ℕ) ≡ c1 [MOD 3 ^ k] := by
        apply (ZMod.natCast_eq_natCast_iff _ _ _).mp; push_cast; exact hW
      exact hh
    rw [hmod, Nat.mod_eq_of_lt hc1lt]
  have h9dvd : (9 : ℕ) ∣ 3 ^ k := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]; exact pow_dvd_pow 3 hk
  refine ⟨W, hc1eq, ?_⟩
  apply mod6_of_two_pow_mod9_seven
  rw [← two_pow_mod_nine]
  calc 2 ^ W % 9 = (2 ^ W % 3 ^ k) % 9 := (Nat.mod_mod_of_dvd _ h9dvd).symm
    _ = c1 % 9 := by rw [← hc1eq]
    _ = 7 := hc19

/-! ### Lemma 5 — the entry zero-edge `InvStart(m+1) → s1` (class 7) -/

/-- **The entry edge.**  From `InvStart(m+1)` (class 1, no one-edge) a single zero-edge (weight
`τ−2 = 2`, hence κ=0) reaches a class-7 vertex `s1 = ⟨1, c1⟩` with `c1 = (3·aS202+1)·2^{-4} mod M`.
`c1` is a unit, so `c1 = 2^W % M` for `W = dlog(c1)`, and `W ≡ 4 (mod 6)` (forced by class 7) —
`W` is the existential bridge to the ladder, never computed.  aS202's value is never used beyond
`aS202 ≡ 1 (mod 9)`. -/
theorem entry_zeroEdge (m : ℕ) (hm : 1 ≤ m) :
    ∃ (c1 W : ℕ),
      InvEdgeZero (22 * (m + 1) + 2) (InvStart (m + 1)) ⟨1, c1⟩ ((tau c1 : Int) - 2) ∧
      tau c1 = 4 ∧
      c1 = 2 ^ W % 3 ^ (22 * (m + 1) + 2 + 1) ∧ W % 6 = 4 := by
  set R := 22 * (m + 1) + 2 with hRdef
  have hStart : (InvStart (m + 1)).c = aS202 := invStart_c_eq_aS202 (m + 1) (by omega)
  have ha9 : aS202 % 9 = 1 := S206_a_mod9
  have h3a9 : (3 * aS202 + 1) % 9 = 4 := by omega
  have hR1 : 1 ≤ R + 1 := by omega
  have hR2 : 2 ≤ R + 1 := by omega
  have h9dvd : (9 : ℕ) ∣ 3 ^ (R + 1) := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]; exact pow_dvd_pow 3 hR2
  have hMpos : 0 < 3 ^ (R + 1) := by positivity
  have hM1lt : 1 < 3 ^ (R + 1) := by
    calc (1 : ℕ) < 3 := by norm_num
      _ = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ (R + 1) := Nat.pow_le_pow_right (by norm_num) hR1
  have hinv9 : invMod2Pow 4 (3 ^ (R + 1)) % 9 = 4 := invMod2Pow_four_mod9 (R + 1) hR2
  set c1 := ((3 * aS202 + 1) * invMod2Pow 4 (3 ^ (R + 1))) % 3 ^ (R + 1) with hc1def
  clear_value c1
  have hc19 : c1 % 9 = 7 := by
    have e : c1 % 9 = ((3 * aS202 + 1) % 9 * (invMod2Pow 4 (3 ^ (R + 1)) % 9)) % 9 := by
      rw [hc1def, Nat.mod_mod_of_dvd _ h9dvd, Nat.mul_mod]
    rw [e, h3a9, hinv9]
  have hc1lt : c1 < 3 ^ (R + 1) := by rw [hc1def]; exact Nat.mod_lt _ hMpos
  have hcons : (3 * aS202 + 1) % 3 ^ (R + 1) = (2 ^ 4 * c1) % 3 ^ (R + 1) := by
    have hcancelMod : (2 ^ 4 * invMod2Pow 4 (3 ^ (R + 1))) % 3 ^ (R + 1) = 1 :=
      invMod2Pow_cancel 4 (R + 1) hR1
    have hkey : 2 ^ 4 * c1 ≡ 3 * aS202 + 1 [MOD 3 ^ (R + 1)] := by
      calc 2 ^ 4 * c1
          = 2 ^ 4 * (((3 * aS202 + 1) * invMod2Pow 4 (3 ^ (R + 1))) % 3 ^ (R + 1)) := by
            rw [hc1def]
        _ ≡ 2 ^ 4 * ((3 * aS202 + 1) * invMod2Pow 4 (3 ^ (R + 1))) [MOD 3 ^ (R + 1)] :=
            (Nat.mod_modEq _ _).mul_left _
        _ = (3 * aS202 + 1) * (2 ^ 4 * invMod2Pow 4 (3 ^ (R + 1))) := by ring
        _ ≡ (3 * aS202 + 1) * 1 [MOD 3 ^ (R + 1)] := by
            have hc : (2 ^ 4 * invMod2Pow 4 (3 ^ (R + 1))) ≡ 1 [MOD 3 ^ (R + 1)] := by
              unfold Nat.ModEq; rw [hcancelMod, Nat.mod_eq_of_lt hM1lt]
            exact hc.mul_left _
        _ = 3 * aS202 + 1 := by rw [mul_one]
    exact hkey.symm
  clear hinv9 hc1def
  have htau : tau c1 = 4 := tau_class_seven c1 hc19
  have hc3 : c1 % 3 = 1 := by omega
  obtain ⟨W, hc1eq, hW6⟩ := unit_eq_two_pow_mod9 (R + 1) c1 hR2 hc3 hc1lt hc19
  refine ⟨c1, W, ?_, htau, hc1eq, hW6⟩
  refine ⟨?_, InX_class_seven c1 hc19, ?_, rfl⟩
  · show (1 : ℕ) = (InvStart (m + 1)).j + 1
    rfl
  · show (3 * (InvStart (m + 1)).c + 1) % 3 ^ (R + 1) = (2 ^ tau c1 * c1) % 3 ^ (R + 1)
    rw [hStart, htau]
    exact hcons

end CollatzLean4.Admissible



