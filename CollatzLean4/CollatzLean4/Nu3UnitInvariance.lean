/-
**3-unit invariance of the capped 3-adic valuation `ν₃`.**

This module proves the single critical-path UNBLOCKER for the discrete-log /
lifting-the-exponent attack on the S202 accessibility barrier:

  * `nu3_unit_mul` — `ν₃(u · x) = ν₃(x)` (capped) whenever `u % 3 ≠ 0`, i.e.
    the capped 3-adic valuation is invariant under multiplication by any
    3-unit. This is the missing ingredient behind BOTH the one-edge
    discrete-log law and the τ=2 "climb" law.

Building on it, this module also formalises:

  * `zeroEdge_tau2_rhoPlus_climb` — **law (2)** of the verified transition
    table: along a τ=2 inverse-zero-edge, `ρ₊` climbs by exactly one,
    `ρ₊(c', R+j') = ρ₊(c, R+j) + 1`. Together with the already-formalised
    τ=1 and τ=3 RESET laws this closes the zero-edge half of the table
    `{τ=1 reset ✓, τ=2 climb ✓, τ=3 reset ✓}`.

HONEST SCOPE: these laws are structural facts about the 3-adic potential
`ρ₊`; they are a down-payment on a possible analytic Bellman–Ford potential
(Route A) for the S202 *slope*-barrier half of the S202 alternative. They are
NOT a proof of Collatz, nor even of the full S202 alternative (which also needs
the subcritical-access branch and the external Bandujar reduction).
-/

import CollatzLean4.S214Core
import CollatzLean4.RhoTransitionLaws
import CollatzLean4.InverseGraph

namespace CollatzLean4.Admissible

/-! ### The 3-unit invariance unblocker -/

/-- **`ν₃(u · x) = ν₃(x)` when `u % 3 ≠ 0`** (capped 3-adic valuation is
invariant under multiplication by a 3-unit).

Proof by induction on the cap `c`, mirroring the recursion of `nu3`.

  * Base `c = 0`: both sides are `nu3 _ 0 = 0` unconditionally.
  * Step `c = c'+1`: dispatch `x = 0` first (then `u*x = 0`, both sides `0`).
    For `x ≠ 0`, `u ≠ 0` (else `u % 3 = 0`), so `u*x ≠ 0`. The key congruence
    `(u*x) % 3 = ((u%3)*(x%3)) % 3` (via `Nat.mul_mod`) together with `u%3 ≠ 0`
    gives `(u*x) % 3 = 0 ↔ x % 3 = 0`.
      - If `x % 3 = 0`: `3 ∣ x`, so `(u*x)/3 = u*(x/3)` (`Nat.mul_div_assoc`,
        which REQUIRES the divisibility — it fails otherwise), and the goal
        reduces to `1 + ν₃(u*(x/3)) c' = 1 + ν₃(x/3) c'`, closed by the IH.
      - If `x % 3 ≠ 0`: both sides vanish by
        `nu3_eq_zero_of_mod_three_ne_zero`. -/
theorem nu3_unit_mul (u x c : Nat) (hu : u % 3 ≠ 0) :
    nu3 (u * x) c = nu3 x c := by
  induction c generalizing x with
  | zero => simp
  | succ c ih =>
      by_cases hx : x = 0
      · subst hx; simp
      · -- u ≠ 0 (otherwise u % 3 = 0).
        have hu0 : u ≠ 0 := by rintro rfl; exact hu (by decide)
        have hux : u * x ≠ 0 := Nat.mul_ne_zero hu0 hx
        -- (u*x) % 3 = ((u%3)*(x%3)) % 3.
        have h_mulmod : (u * x) % 3 = ((u % 3) * (x % 3)) % 3 := Nat.mul_mod u x 3
        by_cases h3 : x % 3 = 0
        · -- 3 ∣ x; (u*x)/3 = u*(x/3).
          have h3dvd : (3 : Nat) ∣ x := Nat.dvd_of_mod_eq_zero h3
          have h_ux_mod3 : (u * x) % 3 = 0 := by
            rw [h_mulmod, h3, Nat.mul_zero]
          have h_div : (u * x) / 3 = u * (x / 3) := Nat.mul_div_assoc u h3dvd
          show (if u * x = 0 then 0
                else if (u * x) % 3 = 0 then 1 + nu3 ((u * x) / 3) c else 0)
               = (if x = 0 then 0
                  else if x % 3 = 0 then 1 + nu3 (x / 3) c else 0)
          rw [if_neg hux, if_pos h_ux_mod3, h_div, if_neg hx, if_pos h3,
              ih (x / 3)]
        · -- x % 3 ≠ 0; both sides are 0.
          rw [nu3_eq_zero_of_mod_three_ne_zero (u * x) (c + 1),
              nu3_eq_zero_of_mod_three_ne_zero x (c + 1) h3]
          rw [h_mulmod]
          -- (u%3) ∈ {1,2}, (x%3) ∈ {1,2}; product mod 3 ≠ 0.
          have hu' : u % 3 = 1 ∨ u % 3 = 2 := by omega
          have hx' : x % 3 = 1 ∨ x % 3 = 2 := by omega
          rcases hu' with h | h <;> rcases hx' with h' | h' <;>
            rw [h, h'] <;> decide

/-! ### Residue invariance of the capped valuation -/

/-- **Congruent (nonzero) representatives have equal capped valuation** at a cap
matching the modulus power: if `a ≡ b (mod 3^c)` with `a ≠ 0` and `b ≠ 0`, then
`nu3 a c = nu3 b c`.

The nonzero hypotheses are essential: the `nu3 0 = 0` convention breaks the
statement at the saturation residue `0` (e.g. `a = 0`, `b = 3^c` are congruent
mod `3^c` but have `nu3 = 0` and `nu3 = c` respectively).

Proof by induction on `c`. The recursion of `nu3` is mirrored by the two
unconditional residue identities `(a % 3^(c+1)) % 3 = a % 3` and
`(a % 3^(c+1)) / 3 = (a / 3) % 3^c`, which transport the congruence to the
quotients. When `3 ∣ a` and `a ≠ 0` we have `a ≥ 3`, hence `a / 3 ≠ 0`, so the
inductive hypothesis applies. -/
theorem nu3_congr_mod_pow :
    ∀ (c a b : Nat), a % 3 ^ c = b % 3 ^ c → a ≠ 0 → b ≠ 0 →
      nu3 a c = nu3 b c := by
  intro c
  induction c with
  | zero => intro a b _ _ _; simp
  | succ c ih =>
      intro a b h ha hb
      -- a % 3 = b % 3 (both sides reduce mod 3, since 3 ∣ 3^(c+1)).
      have h3dvd : (3 : Nat) ∣ 3 ^ (c + 1) := dvd_pow_self 3 (Nat.succ_ne_zero c)
      have ha3 : a % 3 = b % 3 := by
        have hLa := Nat.mod_mod_of_dvd a h3dvd
        have hLb := Nat.mod_mod_of_dvd b h3dvd
        rw [← hLa, h, hLb]
      by_cases hn3 : a % 3 = 0
      · -- 3 ∣ a (and 3 ∣ b). Recurse on the quotients.
        have hn3b : b % 3 = 0 := by rw [← ha3]; exact hn3
        -- a ≥ 3 (nonzero multiple of 3), so a / 3 ≠ 0; likewise b.
        have ha_div_ne : a / 3 ≠ 0 := by
          rcases Nat.eq_zero_or_pos (a / 3) with h0 | hpos
          · exfalso; have := Nat.div_add_mod a 3; rw [h0, hn3] at this; omega
          · omega
        have hb_div_ne : b / 3 ≠ 0 := by
          rcases Nat.eq_zero_or_pos (b / 3) with h0 | hpos
          · exfalso; have := Nat.div_add_mod b 3; rw [h0, hn3b] at this; omega
          · omega
        -- (a/3) % 3^c = (b/3) % 3^c, via the unconditional mod/div identity.
        have h_div_id : ∀ n : Nat, (n % 3 ^ (c + 1)) / 3 = (n / 3) % 3 ^ c := by
          intro n
          rw [pow_succ, Nat.mul_comm (3 ^ c) 3]
          exact Nat.mod_mul_right_div_self n 3 (3 ^ c)
        have h_quot : (a / 3) % 3 ^ c = (b / 3) % 3 ^ c := by
          rw [← h_div_id a, ← h_div_id b, h]
        have h_lhs : nu3 a (c + 1) = 1 + nu3 (a / 3) c := by
          show (if a = 0 then 0
                else if a % 3 = 0 then 1 + nu3 (a / 3) c else 0) = _
          rw [if_neg ha, if_pos hn3]
        have h_rhs : nu3 b (c + 1) = 1 + nu3 (b / 3) c := by
          show (if b = 0 then 0
                else if b % 3 = 0 then 1 + nu3 (b / 3) c else 0) = _
          rw [if_neg hb, if_pos hn3b]
        rw [h_lhs, h_rhs, ih (a / 3) (b / 3) h_quot ha_div_ne hb_div_ne]
      · -- 3 ∤ a (and 3 ∤ b): both valuations vanish.
        have hn3b : b % 3 ≠ 0 := by rw [← ha3]; exact hn3
        rw [nu3_eq_zero_of_mod_three_ne_zero a (c + 1) hn3,
            nu3_eq_zero_of_mod_three_ne_zero b (c + 1) hn3b]

/-! ### The τ=2 climb law -/

/-- A `τ = 2` value has `v'.c ≡ 1` or `≡ 4 (mod 9)` (the two residues mapped to
`2` by the `tau` table). -/
theorem mod9_of_tau_eq_two {n : Nat} (h : tau n = 2) :
    n % 9 = 1 ∨ n % 9 = 4 := by
  rw [tau_mod] at h
  have h9 : n % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases (n % 9) <;> simp_all [tau]

/-- **τ=2 CLEAN CLIMB law** (law (2) of the verified transition table).

Along a `τ(v'.c) = 2` inverse-zero-edge, the root-proximity `ρ₊` climbs by
exactly one:
\[
  \rho_+(v'.c,\ R + v'.j) \;=\; \rho_+(v.c,\ R + v.j) + 1.
\]

*Proof.* Write `r := R + v.j`, so `R + v'.j = r + 1`. The `InvEdgeZero`
consistency for `τ = 2` reads `3·v.c + 1 ≡ 4·v'.c (mod 3^{r+1})`. Reducing it
mod `9` against `v'.c mod 9 ∈ {1, 4}` forces `v.c % 3 ∈ {1, 2}`, in particular
`v.c ≠ 0`; together with `v.c ≠ 1` this gives `v.c ≥ 2`, so `v.c - 1 ≠ 0`.
Also `v'.c ≥ 1`.

From the congruence, `4·(v'.c − 1) ≡ 3·(v.c − 1) (mod 3^{r+1})` (honest in `ℕ`
because `v'.c ≥ 1`, `v.c ≥ 1`). Then, with `v'.c ≠ 1`:
\[
  \rho_+(v'.c, r{+}1) = \nu_3(v'.c{-}1, r{+}1)
    \overset{\text{unit }4}{=} \nu_3(4(v'.c{-}1), r{+}1)
    \overset{\text{congr}}{=} \nu_3(3(v.c{-}1), r{+}1)
    \overset{\nu_3(3\cdot), \, v.c-1\neq0}{=} \nu_3(v.c{-}1, r) + 1
    = \rho_+(v.c, r) + 1.
\]
The boundary case `v'.c = 1` is handled separately: then `3·(v.c−1) ≡ 0`, so
`3^r ∣ (v.c − 1)`, giving `ρ₊(v.c, r) = r` and `ρ₊(1, r+1) = r + 1`. -/
theorem zeroEdge_tau2_rhoPlus_climb
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_zero : InvEdgeZero R v v' ω) (h_tau : tau v'.c = 2)
    (h_v_can : v.c < 3 ^ (R + v.j)) (_h_v'_can : v'.c < 3 ^ (R + v'.j))
    (h_v_ne1 : v.c ≠ 1) :
    rhoPlus v'.c (R + v'.j) = rhoPlus v.c (R + v.j) + 1 := by
  obtain ⟨h_j_eq, _h_X, h_consistency, _h_ω⟩ := h_zero
  -- Abbreviate the cap `r := R + v.j`; note `R + v'.j = r + 1`.
  have h_j' : R + v'.j = R + v.j + 1 := by omega
  -- τ=2 ⇒ 2^τ = 4.
  have h_pow4 : (2 : Nat) ^ tau v'.c = 4 := by rw [h_tau]; norm_num
  rw [h_pow4] at h_consistency
  -- The cap on the target side is ≥ 2 (since R ≥ 1, v'.j ≥ 1).
  have h_rj'_ge2 : 2 ≤ R + v'.j := by omega
  -- v'.c % 9 ∈ {1,4}; hence v'.c ≥ 1.
  have h_v'_mod9 := mod9_of_tau_eq_two h_tau
  have h_v'_ge1 : 1 ≤ v'.c := by rcases h_v'_mod9 with h | h <;> omega
  -- Reduce the consistency mod 9 to pin v.c % 3 ≠ 0.
  have h9dvd : (9 : Nat) ∣ 3 ^ (R + v'.j) := by
    have : (9 : Nat) = 3 ^ 2 := by norm_num
    rw [this]; exact pow_dvd_pow 3 h_rj'_ge2
  have hL9 := Nat.mod_mod_of_dvd (3 * v.c + 1) h9dvd
  have hR9 := Nat.mod_mod_of_dvd (4 * v'.c) h9dvd
  have h_mod9 : (3 * v.c + 1) % 9 = (4 * v'.c) % 9 := by
    rw [← hL9, h_consistency, hR9]
  -- (4 * v'.c) % 9 is 4 (if v'.c ≡ 1) or 7 (if v'.c ≡ 4).
  have h_4vc_mod9 : (4 * v'.c) % 9 = 4 ∨ (4 * v'.c) % 9 = 7 := by
    rw [Nat.mul_mod]
    rcases h_v'_mod9 with h | h <;> rw [h]
    · left; rfl
    · right; rfl
  -- v.c % 3 ≠ 0 (so v.c ≠ 0): otherwise (3*v.c+1) % 9 = 1 ∉ {4,7}.
  have h_vc_mod3 : v.c % 3 ≠ 0 := by
    rcases h_4vc_mod9 with h | h <;> rw [h] at h_mod9 <;> omega
  have h_vc_ge2 : 2 ≤ v.c := by
    rcases Nat.lt_or_ge v.c 2 with h | h
    · interval_cases v.c <;> simp_all
    · exact h
  have h_vc_sub_ne : v.c - 1 ≠ 0 := by omega
  -- Core congruence: 4*(v'.c - 1) ≡ 3*(v.c - 1) (mod 3^(R+v'.j)).
  have h_core : (4 * (v'.c - 1)) % 3 ^ (R + v'.j)
      = (3 * (v.c - 1)) % 3 ^ (R + v'.j) := by
    -- Reassociate 4*(v'.c-1) into 4*v'.c, then telescope through the edge
    -- congruence `4*v'.c ≡ 3*v.c+1` and cancel the additive `+4`.
    have e1 : 4 * (v'.c - 1) + 4 = 4 * v'.c := by omega
    have hM : 3 * v.c + 1 ≡ 4 * v'.c [MOD 3 ^ (R + v'.j)] := h_consistency
    have h4 : 4 * (v'.c - 1) + 4 ≡ 3 * (v.c - 1) + 4 [MOD 3 ^ (R + v'.j)] := by
      rw [e1]
      calc 4 * v'.c ≡ 3 * v.c + 1 [MOD 3 ^ (R + v'.j)] := hM.symm
        _ = 3 * (v.c - 1) + 4 := by omega
    exact Nat.ModEq.add_right_cancel' 4 h4
  -- Main case split on whether v'.c = 1.
  by_cases h_v'_eq1 : v'.c = 1
  · -- Boundary: v'.c = 1 ⇒ rhoPlus v'.c (r+1) = r+1; show rhoPlus v.c r = r.
    -- From h_core with v'.c = 1: 0 ≡ 3*(v.c-1), so 3^(R+v'.j) ∣ 3*(v.c-1).
    have h_core' : (3 * (v.c - 1)) % 3 ^ (R + v'.j) = 0 := by
      rw [← h_core, h_v'_eq1]; simp
    have h_dvd : 3 ^ (R + v'.j) ∣ 3 * (v.c - 1) := Nat.dvd_of_mod_eq_zero h_core'
    -- 3^(R+v'.j) = 3^(R+v.j+1) = 3 * 3^(R+v.j); cancel the 3.
    have h_dvd_r : 3 ^ (R + v.j) ∣ (v.c - 1) := by
      have hpow : 3 ^ (R + v'.j) = 3 * 3 ^ (R + v.j) := by
        rw [h_j', pow_succ, Nat.mul_comm]
      rw [hpow] at h_dvd
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp h_dvd
    have h_rp_v : rhoPlus v.c (R + v.j) = R + v.j := by
      unfold rhoPlus
      rw [if_neg h_v_ne1, nu3_eq_cap_of_dvd (R + v.j) (v.c - 1) h_vc_sub_ne h_dvd_r]
    have h_rp_v' : rhoPlus v'.c (R + v'.j) = R + v'.j := by
      unfold rhoPlus; rw [h_v'_eq1]; simp
    rw [h_rp_v, h_rp_v', h_j']
  · -- Main case: v'.c ≠ 1 ⇒ both rhoPlus values are nu3 of (·-1).
    have h_rp_v : rhoPlus v.c (R + v.j) = nu3 (v.c - 1) (R + v.j) := by
      unfold rhoPlus; rw [if_neg h_v_ne1]
    have h_rp_v' : rhoPlus v'.c (R + v'.j) = nu3 (v'.c - 1) (R + v'.j) := by
      unfold rhoPlus; rw [if_neg h_v'_eq1]
    rw [h_rp_v, h_rp_v']
    -- nu3(v'.c-1)(r+1) = nu3(4*(v'.c-1))(r+1)  [unit 4]
    have hu4 : (4 : Nat) % 3 ≠ 0 := by decide
    have h_unit : nu3 (4 * (v'.c - 1)) (R + v'.j) = nu3 (v'.c - 1) (R + v'.j) :=
      nu3_unit_mul 4 (v'.c - 1) (R + v'.j) hu4
    -- nu3(4*(v'.c-1))(r+1) = nu3(3*(v.c-1))(r+1)  [congruence], with both nonzero.
    have h4ne : 4 * (v'.c - 1) ≠ 0 := by
      have : v'.c - 1 ≠ 0 := by omega
      exact Nat.mul_ne_zero (by decide) this
    have h3ne : 3 * (v.c - 1) ≠ 0 := Nat.mul_ne_zero (by decide) h_vc_sub_ne
    have h_congr : nu3 (4 * (v'.c - 1)) (R + v'.j) = nu3 (3 * (v.c - 1)) (R + v'.j) :=
      nu3_congr_mod_pow (R + v'.j) _ _ h_core h4ne h3ne
    -- nu3(3*(v.c-1))(r+1) = nu3(v.c-1) r + 1  [extract factor 3], using r+1 = (R+v.j)+1.
    have h_three : nu3 (3 * (v.c - 1)) (R + v'.j) = nu3 (v.c - 1) (R + v.j) + 1 := by
      rw [h_j']
      exact nu3_mul_three (v.c - 1) (R + v.j) h_vc_sub_ne
    rw [← h_unit, h_congr, h_three]

end CollatzLean4.Admissible
