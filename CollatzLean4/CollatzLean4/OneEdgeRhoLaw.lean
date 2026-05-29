/-
**One-edge 3-adic discrete-log law for inverse-cylinder edges (law 1).**

This module proves **law (1)** of the verified transition table
(`tools/structure_probe.py`, 0 violations): along an `InvEdgeOne` (inverse of
`Branch.one`, which preserves the zero-step count `j`), the root-proximity
potential `ρ₊` of the *target* cylinder is the capped 3-adic valuation of
`c − 2^τ`:
\[
  \rho_+(v'.c,\ R + v'.j) \;=\; \nu_3\bigl((v.c - 2^{\tau})\bmod 3^{R+v.j}\bigr),
  \qquad \tau = \tau(v'.c).
\]

  * `oneEdge_threeUnit_inv` — the modular inverse `invMod2Pow τ (3^r)` is a
    3-unit (`% 3 ≠ 0`), the hypothesis needed to invoke `nu3_unit_mul`.
  * `oneEdge_discreteLog` — the discrete-log inversion specialised to one-edges:
    `invMod2Pow τ M * v.c ≡ v'.c (mod M)` (re-derivation of the inversion already
    used inside `outgoingEdges_complete_one`).
  * `oneEdge_rhoPlus_law` — the main law.

HONEST SCOPE / form of the statement.  The verified probe computes the RHS as
`nu3((c - 2^τ) % M)` where `c - 2^τ` is the **integer** subtraction reduced
mod `M = 3^r`.  In `ℕ` the truncating subtraction `v.c - 2^τ` is *wrong* whenever
`v.c < 2^τ` (which the hypotheses do not exclude — `v.c` need not even be
canonical).  We therefore render the integer residue faithfully and without any
truncation as
\[
  (v.c - 2^{\tau})\bmod M \;=\; \bigl(v.c + (M - 2^{\tau}\bmod M)\bigr)\bmod M ,
\]
i.e. the RHS is `nu3 ((v.c + (3^r - 2^τ % 3^r)) % 3^r) r`.  This is the exact,
always-correct `ℕ` transcription of the probe's `nu3((c - 2^τ) % M)`; the
adjustment is purely about representing a `ℤ`-residue inside `ℕ`.

These laws are structural facts about the 3-adic potential `ρ₊`; they are a
down-payment on a possible analytic Bellman–Ford potential (Route A) for the
S202 *slope*-barrier half of the S202 alternative.  They are NOT a proof of
Collatz, nor even of the full S202 alternative (which also needs the
subcritical-access branch and the external Bandújar reduction).
-/

import CollatzLean4.Nu3UnitInvariance

namespace CollatzLean4.Admissible

/-! ### The modular inverse `invMod2Pow τ (3^r)` is a 3-unit -/

/-- **`invMod2Pow τ (3^r)` is a 3-unit** (`% 3 ≠ 0`) for `r ≥ 1`.

`2^τ · invMod2Pow τ (3^r) ≡ 1 (mod 3^r)` (`two_pow_mul_invMod2Pow_three_pow`),
and `3 ∣ 3^r`, so reducing further mod `3` gives `2^τ · u ≡ 1 (mod 3)`.  Were
`u := invMod2Pow τ (3^r)` divisible by `3`, the LHS would be `≡ 0 (mod 3)`,
contradicting `≡ 1`. -/
theorem oneEdge_threeUnit_inv (τ r : Nat) (hr : 1 ≤ r) :
    invMod2Pow τ (3 ^ r) % 3 ≠ 0 := by
  intro hu0
  -- `2^τ · u ≡ 1 (mod 3^r)`, with `u := invMod2Pow τ (3^r)`.
  have h_inv : (2 ^ τ * invMod2 (3 ^ r) ^ τ) % (3 ^ r) = 1 % (3 ^ r) :=
    two_pow_mul_invMod2Pow_three_pow r τ hr
  -- Reduce both sides further mod 3 (since `3 ∣ 3^r`).
  have h3dvd : (3 : Nat) ∣ 3 ^ r := dvd_pow_self 3 (by omega : r ≠ 0)
  -- `(2^τ · u) % 3 = 1 % 3 = 1`, where `u = invMod2 (3^r) ^ τ`.
  have hL := Nat.mod_mod_of_dvd (2 ^ τ * invMod2 (3 ^ r) ^ τ) h3dvd
  have hRr := Nat.mod_mod_of_dvd (1 : Nat) h3dvd
  have h_mod3 : (2 ^ τ * invMod2 (3 ^ r) ^ τ) % 3 = 1 % 3 := by
    rw [← hL, h_inv, hRr]
  -- But `invMod2Pow τ (3^r) = invMod2 (3^r) ^ τ % 3^r`; `u % 3 = 0` forces the
  -- product `% 3 = 0`.
  have hu_unfold : invMod2Pow τ (3 ^ r) = invMod2 (3 ^ r) ^ τ % 3 ^ r := rfl
  rw [hu_unfold] at hu0
  -- `invMod2 (3^r) ^ τ % 3 = (invMod2 (3^r) ^ τ % 3^r) % 3 = 0`.
  have h_base_mod3 : invMod2 (3 ^ r) ^ τ % 3 = 0 := by
    have := Nat.mod_mod_of_dvd (invMod2 (3 ^ r) ^ τ) h3dvd
    rw [← this, hu0]
  -- Then `(2^τ · u) % 3 = (2^τ % 3 · (u % 3)) % 3 = 0`, contradiction with `= 1`.
  rw [Nat.mul_mod, h_base_mod3, Nat.mul_zero] at h_mod3
  simp at h_mod3

/-! ### One-edge discrete-log inversion -/

/-- **One-edge discrete-log inversion.**  For an `InvEdgeOne` with `r := R+v.j ≥ 1`,
the consistency `v.c ≡ 2^τ · v'.c (mod 3^r)` inverts to
`invMod2Pow τ (3^r) · v.c ≡ v'.c (mod 3^r)`.

(Re-derivation of the inversion already performed inside
`outgoingEdges_complete_one`, packaged as a reusable lemma.) -/
theorem oneEdge_discreteLog
    {R : Nat} {v v' : InvVertex} {ω : Int}
    (h_one : InvEdgeOne R v v' ω) (hr : 1 ≤ R + v.j) :
    invMod2Pow (tau v'.c) (3 ^ (R + v.j)) * v.c ≡ v'.c [MOD 3 ^ (R + v.j)] := by
  obtain ⟨_h_j, _h_X, h_cong, _h_ω⟩ := h_one
  set M := 3 ^ (R + v.j) with hM
  -- `2^τ · invMod2 M ^ τ ≡ 1 (mod M)`.
  have h_inv : 2 ^ tau v'.c * invMod2 M ^ tau v'.c ≡ 1 [MOD M] := by
    show (2 ^ tau v'.c * invMod2 M ^ tau v'.c) % M = 1 % M
    exact two_pow_mul_invMod2Pow_three_pow _ _ hr
  have h_cong' : v.c ≡ 2 ^ tau v'.c * v'.c [MOD M] := h_cong
  unfold invMod2Pow
  have step1 : invMod2 M ^ tau v'.c % M * v.c ≡ invMod2 M ^ tau v'.c * v.c [MOD M] := by
    show (invMod2 M ^ tau v'.c % M * v.c) % M = (invMod2 M ^ tau v'.c * v.c) % M
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  calc invMod2 M ^ tau v'.c % M * v.c
      ≡ invMod2 M ^ tau v'.c * v.c [MOD M] := step1
    _ ≡ invMod2 M ^ tau v'.c * (2 ^ tau v'.c * v'.c) [MOD M] := h_cong'.mul_left _
    _ = (2 ^ tau v'.c * invMod2 M ^ tau v'.c) * v'.c := by ring
    _ ≡ 1 * v'.c [MOD M] := h_inv.mul_right _
    _ = v'.c := by ring

/-! ### The main one-edge ρ₊ law -/

/-- **One-edge discrete-log law** (law (1) of the verified transition table).

Along an `InvEdgeOne` (which preserves `j`, so `R + v'.j = R + v.j =: r`), the
root-proximity `ρ₊` of the target cylinder is the capped 3-adic valuation of
`c − 2^τ` reduced mod `3^r`:
\[
  \rho_+(v'.c,\ R + v'.j) \;=\; \nu_3\bigl((v.c - 2^{\tau})\bmod 3^{r}\bigr),
  \qquad \tau = \tau(v'.c),
\]
rendered in `ℕ` (without truncation) as
`nu3 ((v.c + (3^r - 2^τ % 3^r)) % 3^r) r`.

*Proof.*  Write `M := 3^r`, `τ := τ(v'.c)`, `u := invMod2Pow τ M`,
`D := M - 2^τ % M` and `w := (v.c + D) % M`.  `InX v'.c` gives `v'.c ≥ 1`, and
`v'.c ≠ 1` together with `v'.c < M` gives `2 ≤ v'.c < M`, so `v'.c − 1` is a
nonzero canonical residue.  The discrete-log inversion gives `u·v.c ≡ v'.c`, and
`2^τ·u ≡ 1` gives `u·D + 1 ≡ 0 (mod M)` (because `D + 2^τ%M = M`).  Hence
`u·w + 1 ≡ u·v.c + (u·D + 1) ≡ v'.c (mod M)`; cancelling the `+1`
(`v'.c = (v'.c−1)+1`) yields `u·w ≡ v'.c − 1 (mod M)`.  Both `v'.c − 1` and
`u·w` are nonzero mod `M`, so `ν₃(v'.c−1) = ν₃(u·w)` by `nu3_congr_mod_pow`, and
stripping the 3-unit `u` (`nu3_unit_mul`) gives `ν₃(u·w) = ν₃(w)`, which is the
claimed RHS. -/
theorem oneEdge_rhoPlus_law
    {R : Nat} (hR : 1 ≤ R) {v v' : InvVertex} {ω : Int}
    (h_one : InvEdgeOne R v v' ω)
    (h_v'_can : v'.c < 3 ^ (R + v'.j)) (h_v'_ne1 : v'.c ≠ 1) :
    rhoPlus v'.c (R + v'.j)
      = nu3 ((v.c + (3 ^ (R + v.j) - 2 ^ tau v'.c % 3 ^ (R + v.j)))
              % 3 ^ (R + v.j)) (R + v.j) := by
  -- Extract the edge fields without consuming `h_one` (needed by
  -- `oneEdge_discreteLog`).
  have h_j_eq : v'.j = v.j := h_one.1
  have h_X : InX v'.c := h_one.2.1
  -- `j` is preserved: `R + v'.j = R + v.j =: r`.
  have h_rj : R + v'.j = R + v.j := by omega
  have hr : 1 ≤ R + v.j := by omega
  set r := R + v.j with hr_def
  set M := 3 ^ r with hM
  set τ := tau v'.c with hτ
  set u := invMod2Pow τ M with hu_def
  set D := M - 2 ^ τ % M with hD
  set w := (v.c + D) % M with hw
  -- `M ≥ 3 ≥ 2`, in particular `M ≠ 0` and `1 < M`.
  have hM_pos : 0 < M := by rw [hM]; positivity
  have h1_lt_M : 1 < M := by
    have h : (3 : Nat) ^ 1 ≤ 3 ^ r := Nat.pow_le_pow_right (by decide) hr
    have : (3 : Nat) ^ 1 = 3 := by ring
    rw [hM]; omega
  -- `v'.c ≥ 1` (from `InX`), hence with `v'.c ≠ 1`, `2 ≤ v'.c`.
  have h_v'_ne0 : v'.c ≠ 0 := by
    intro h0; rw [h0] at h_X; unfold InX at h_X; simp at h_X
  have h_v'_ge2 : 2 ≤ v'.c := by omega
  have h_v'_sub_ne : v'.c - 1 ≠ 0 := by omega
  -- `v'.c - 1 < M` (canonicality, transported through `h_rj`).
  have h_v'_can_r : v'.c < M := by rw [hM, ← h_rj]; exact h_v'_can
  -- `u` is a 3-unit.
  have hu_unit : u % 3 ≠ 0 := by rw [hu_def, hM]; exact oneEdge_threeUnit_inv τ r hr
  -- Discrete-log inversion: `u · v.c ≡ v'.c (mod M)`.  (The lemma's `R + v.j`,
  -- `tau v'.c`, `3^(R+v.j)` fold definitionally to `r`, `τ`, `M`.)
  have hA : u * v.c ≡ v'.c [MOD M] := oneEdge_discreteLog h_one hr
  -- `2^τ · u ≡ 1 (mod M)`.  Note `u = invMod2 M ^ τ % M`, so the inner `% M`
  -- must be absorbed before applying `two_pow_mul_invMod2Pow_three_pow`
  -- (which is stated with `invMod2 M ^ τ`, no inner mod).
  have h_inv : 2 ^ τ * u ≡ 1 [MOD M] := by
    show (2 ^ τ * u) % M = 1 % M
    have hu_eq : u = invMod2 M ^ τ % M := rfl
    rw [hu_eq, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hM, hτ]
    exact two_pow_mul_invMod2Pow_three_pow r (tau v'.c) hr
  -- `D + 2^τ % M = M`  (since `2^τ % M < M`).
  have hD_add : D + 2 ^ τ % M = M := by
    have h_lt : 2 ^ τ % M < M := Nat.mod_lt _ hM_pos
    rw [hD]; omega
  -- Key: `u · D + 1 ≡ 0 (mod M)`.
  have hB : u * D + 1 ≡ 0 [MOD M] := by
    -- `u·(2^τ % M) ≡ u·2^τ ≡ 1 (mod M)`.
    have hu_mod : u * (2 ^ τ % M) ≡ u * 2 ^ τ [MOD M] := by
      show (u * (2 ^ τ % M)) % M = (u * 2 ^ τ) % M
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    have hu_pow : u * 2 ^ τ ≡ 1 [MOD M] := by
      calc u * 2 ^ τ = 2 ^ τ * u := by ring
        _ ≡ 1 [MOD M] := h_inv
    have hu_pmod1 : u * (2 ^ τ % M) ≡ 1 [MOD M] := hu_mod.trans hu_pow
    -- `u·D + u·(2^τ % M) = u·M ≡ 0`.
    have h_uM : u * D + u * (2 ^ τ % M) = u * M := by
      rw [← Nat.mul_add, hD_add]
    have h_uM_zero : u * M ≡ 0 [MOD M] := by
      show (u * M) % M = 0 % M
      rw [Nat.mul_mod_left]; simp
    -- Conclude `u·D + 1 ≡ u·D + u·(2^τ%M) ≡ 0`.
    calc u * D + 1
        ≡ u * D + u * (2 ^ τ % M) [MOD M] := (Nat.ModEq.refl _).add hu_pmod1.symm
      _ = u * M := h_uM
      _ ≡ 0 [MOD M] := h_uM_zero
  -- `u · w ≡ u · (v.c + D) (mod M)`  (the inner `% M` in `w` is harmless).
  have hw_inv : u * w ≡ u * (v.c + D) [MOD M] := by
    show (u * w) % M = (u * (v.c + D)) % M
    rw [hw, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  -- `u·w + 1 ≡ v'.c (mod M)`.
  have h_uw1 : u * w + 1 ≡ v'.c [MOD M] := by
    calc u * w + 1
        ≡ u * (v.c + D) + 1 [MOD M] := hw_inv.add_right 1
      _ = u * v.c + (u * D + 1) := by ring
      _ ≡ v'.c + 0 [MOD M] := hA.add hB
      _ = v'.c := by ring
  -- Cancel the `+1`: `u·w ≡ v'.c − 1 (mod M)`  (using `v'.c = (v'.c − 1) + 1`).
  have h_uw : u * w ≡ v'.c - 1 [MOD M] := by
    apply Nat.ModEq.add_right_cancel' 1
    calc u * w + 1 ≡ v'.c [MOD M] := h_uw1
      _ = (v'.c - 1) + 1 := by omega
  -- `u·w ≠ 0`:  else `v'.c − 1 ≡ 0`, but `0 < v'.c − 1 < M`.
  have h_uw_ne : u * w ≠ 0 := by
    intro h0
    have : (0 : Nat) ≡ v'.c - 1 [MOD M] := by rw [← h0]; exact h_uw
    have h_dvd : M ∣ (v'.c - 1) := by
      have := this.symm
      rwa [Nat.modEq_zero_iff_dvd] at this
    have h_lt : v'.c - 1 < M := by omega
    have := Nat.le_of_dvd (by omega) h_dvd
    omega
  -- Assemble: `ρ₊ v'.c r = nu3 (v'.c − 1) r = nu3 (u·w) r = nu3 w r`.
  have h_rp : rhoPlus v'.c (R + v'.j) = nu3 (v'.c - 1) r := by
    rw [h_rj]; unfold rhoPlus; rw [if_neg h_v'_ne1]
  rw [h_rp]
  -- `nu3 (v'.c − 1) r = nu3 (u·w) r`  (congruent nonzero representatives).
  have h_congr : nu3 (v'.c - 1) r = nu3 (u * w) r :=
    nu3_congr_mod_pow r (v'.c - 1) (u * w) h_uw.symm h_v'_sub_ne h_uw_ne
  rw [h_congr]
  -- Strip the 3-unit `u`:  `nu3 (u·w) r = nu3 w r`.
  rw [nu3_unit_mul u w r hu_unit]
