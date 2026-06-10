/-
S241 — The bit-length potential: route-B's first WORKING closed-form potential
(bounded-`Q` regime).

Discovered by the S241 archimedean gate (tools/phi_archimedean_gate.py +
phi_quotient_refuter.py): archimedean features cannot EXPRESS the κ-value tables (same
as tropical), but — unlike every previously tested class — they support valid
SUBSOLUTIONS.  The candidate, validated on 137 567 real edges with 0 violations and
confirmed by new engine certificates it predicted (m=1: Q=6 certifies T=2, Q=7
certifies T=1):

    Φ(v) := ⌊(size(v.c mod 3^(R+j)) − 1)/4⌋ + j − Q        (size = binary bit-length)

The three potential obligations are ELEMENTARY (this module):
  * one-edge (κ=+1): `canon v = (2^τ·canon v') mod M ≤ 2^τ·canon v'` ⟹ size grows by
    `≤ τ ≤ 4` backwards ⟹ the floor term drops by ≤ 1;
  * zero-edge: `3·canon v + 1 = (2^τ·canon v') mod M₁ ≤ 2^τ·canon v'` and
    `size(3x+1) ≥ size x + 1` ⟹ `size v + 1 ≤ size v' + τ`; for τ=1 (κ=−1) the size is
    non-decreasing and the `j`-term pays the −1; for τ≥2 (κ=0) the floor drops ≤ 1
    against the `j`-term's +1;
  * goal: `canon = 1` ⟹ Φ = j − Q ≤ 0; start: Φ ≥ m ⟺ `4(m+Q)+1 ≤ size(aS202 mod 3^R)`.

CONSEQUENCE: `S202_kappa_precise_barrier_bounded m Q` holds in CLOSED FORM whenever
`4(m+Q)+1 ≤ size(aS202 mod 3^(22m+2))` — non-inductive, no `native_decide`, subsuming
and EXTENDING the per-instance κ certificates (`kappa_barrier_m1_Q7`: m=1 up to Q=7,
beyond the Q≤5 certificate range).  Under the current `InvStart` (the Caveat-C fixed
`aS202 = 1+3²²`, size 35) the hypothesis caps at `m+Q ≤ 8`; the faithful per-`m` tower
(`aS202_at m`, B₀ ≈ 34.9m bits) would give `Q ≲ 7.7m` — deferred with Caveat C.

HONEST LIMITS: this is the archimedean-shrinkage-budget regime.  Every potential linear
in (bit-length, j) provably dies at `Q ~ 22m`; the large-`Q` wall (the dlog/Baker core)
is untouched.  Route-B for unbounded `Q` remains open — now sharply isolated at
`Q ≳ 8m`.

Axioms target: {propext, Classical.choice, Quot.sound} (+ aS202 anchors only through
the consumer's imports).  Builds narrow.
-/

import CollatzLean4.AnalyticBarrier
import Mathlib.Data.Nat.Size

namespace CollatzLean4.Admissible

/-! ### Size toolbox -/

/-- `τ ≤ 4` always. -/
theorem tau_le_four (n : ℕ) : tau n ≤ 4 := by
  unfold tau
  split <;> omega

/-- `size (2^τ · x) = size x + τ` for `x ≠ 0`. -/
theorem size_two_pow_mul (τ x : ℕ) (hx : x ≠ 0) :
    Nat.size (2 ^ τ * x) = Nat.size x + τ := by
  rw [show 2 ^ τ * x = x <<< τ from by rw [Nat.shiftLeft_eq]; ring]
  exact Nat.size_shiftLeft hx τ

/-- `size (3x+1) ≥ size x + 1`. -/
theorem size_three_mul_add_one (x : ℕ) : Nat.size x + 1 ≤ Nat.size (3 * x + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [Nat.size_one]
  · have h2 : Nat.size (2 ^ 1 * x) = Nat.size x + 1 := size_two_pow_mul 1 x (by omega)
    have hle : 2 ^ 1 * x ≤ 3 * x + 1 := by
      have h21 : (2 : ℕ) ^ 1 = 2 := pow_one 2
      omega
    calc Nat.size x + 1 = Nat.size (2 ^ 1 * x) := h2.symm
      _ ≤ Nat.size (3 * x + 1) := Nat.size_le_size hle

/-- The canonical residue of an admissible value is nonzero. -/
theorem canon_ne_zero_of_InX {c k : ℕ} (hX : InX c) (hk : 1 ≤ k) :
    c % 3 ^ k ≠ 0 := by
  have h3 : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have h93 : c % 3 ^ k % 3 = c % 3 := Nat.mod_mod_of_dvd c h3
  have h9 : c % 9 % 3 = c % 3 := Nat.mod_mod_of_dvd c (by norm_num)
  unfold InX at hX
  intro h0
  rw [h0] at h93
  omega

/-! ### The per-edge size laws -/

/-- **One-edge size law**: the canonical size grows by at most `τ ≤ 4` backwards. -/
theorem oneEdge_size_le {R : ℕ} {v v' : InvVertex} {ω : Int} (hR : 1 ≤ R)
    (he : InvEdgeOne R v v' ω) :
    Nat.size (v.c % 3 ^ (R + v.j)) ≤ Nat.size (v'.c % 3 ^ (R + v.j)) + 4 := by
  obtain ⟨hj, hX', hcong, hω⟩ := he
  have hcanon' : v'.c % 3 ^ (R + v.j) ≠ 0 :=
    canon_ne_zero_of_InX hX' (by omega)
  have hmm : (2 ^ tau v'.c * v'.c) % 3 ^ (R + v.j)
      = (2 ^ tau v'.c * (v'.c % 3 ^ (R + v.j))) % 3 ^ (R + v.j) := by
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl _)]
  have hle : v.c % 3 ^ (R + v.j) ≤ 2 ^ tau v'.c * (v'.c % 3 ^ (R + v.j)) := by
    rw [hcong, hmm]
    exact Nat.mod_le _ _
  calc Nat.size (v.c % 3 ^ (R + v.j))
      ≤ Nat.size (2 ^ tau v'.c * (v'.c % 3 ^ (R + v.j))) := Nat.size_le_size hle
    _ = Nat.size (v'.c % 3 ^ (R + v.j)) + tau v'.c := size_two_pow_mul _ _ hcanon'
    _ ≤ Nat.size (v'.c % 3 ^ (R + v.j)) + 4 := by
        have := tau_le_four v'.c
        omega

/-- **Zero-edge size law**: `size(canon v) + 1 ≤ size(canon v') + τ`. -/
theorem zeroEdge_size_le {R : ℕ} {v v' : InvVertex} {ω : Int} (hR : 1 ≤ R)
    (he : InvEdgeZero R v v' ω) :
    Nat.size (v.c % 3 ^ (R + v.j)) + 1
      ≤ Nat.size (v'.c % 3 ^ (R + v'.j)) + tau v'.c := by
  obtain ⟨hj, hX', hcong, hω⟩ := he
  have hcanon' : v'.c % 3 ^ (R + v'.j) ≠ 0 :=
    canon_ne_zero_of_InX hX' (by omega)
  -- the target modulus is 3 · (source modulus)
  have hM1 : (3 : ℕ) ^ (R + v'.j) = 3 * 3 ^ (R + v.j) := by
    rw [hj, show R + (v.j + 1) = (R + v.j) + 1 from by omega, pow_succ]
    ring
  -- 3·canon(v)+1 is the canonical value of 3·v.c+1 at the target modulus
  have hpos : 0 < (3 : ℕ) ^ (R + v.j) := pow_pos (by norm_num) _
  have hlt : 3 * (v.c % 3 ^ (R + v.j)) + 1 < 3 * 3 ^ (R + v.j) := by
    have := Nat.mod_lt v.c hpos
    omega
  have h2 : (3 * v.c) % (3 * 3 ^ (R + v.j))
      = (3 * (v.c % 3 ^ (R + v.j))) % (3 * 3 ^ (R + v.j)) := by
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
        Nat.mod_mod_of_dvd _ (dvd_refl _)]
  have hme : 3 * v.c + 1 ≡ 3 * (v.c % 3 ^ (R + v.j)) + 1 [MOD 3 * 3 ^ (R + v.j)] :=
    Nat.ModEq.add_right 1 h2
  have hcanon_eq : (3 * v.c + 1) % (3 * 3 ^ (R + v.j))
      = 3 * (v.c % 3 ^ (R + v.j)) + 1 := by
    have h : (3 * v.c + 1) % (3 * 3 ^ (R + v.j))
        = (3 * (v.c % 3 ^ (R + v.j)) + 1) % (3 * 3 ^ (R + v.j)) := hme
    rwa [Nat.mod_eq_of_lt hlt] at h
  -- 3·canon(v)+1 = (2^τ·canon v') mod M₁ ≤ 2^τ·canon v'
  have hmm : (2 ^ tau v'.c * v'.c) % 3 ^ (R + v'.j)
      = (2 ^ tau v'.c * (v'.c % 3 ^ (R + v'.j))) % 3 ^ (R + v'.j) := by
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl _)]
  have hkey : 3 * (v.c % 3 ^ (R + v.j)) + 1
      ≤ 2 ^ tau v'.c * (v'.c % 3 ^ (R + v'.j)) := by
    calc 3 * (v.c % 3 ^ (R + v.j)) + 1
        = (3 * v.c + 1) % (3 * 3 ^ (R + v.j)) := hcanon_eq.symm
      _ = (3 * v.c + 1) % 3 ^ (R + v'.j) := by rw [hM1]
      _ = (2 ^ tau v'.c * (v'.c % 3 ^ (R + v'.j))) % 3 ^ (R + v'.j) := by
          rw [hcong, hmm]
      _ ≤ 2 ^ tau v'.c * (v'.c % 3 ^ (R + v'.j)) := Nat.mod_le _ _
  calc Nat.size (v.c % 3 ^ (R + v.j)) + 1
      ≤ Nat.size (3 * (v.c % 3 ^ (R + v.j)) + 1) := size_three_mul_add_one _
    _ ≤ Nat.size (2 ^ tau v'.c * (v'.c % 3 ^ (R + v'.j))) := Nat.size_le_size hkey
    _ = Nat.size (v'.c % 3 ^ (R + v'.j)) + tau v'.c := size_two_pow_mul _ _ hcanon'

/-! ### The potential and the barrier -/

/-- **The bit-length potential** — route-B's first working closed-form potential:
`Φ(v) = ⌊(size(canon v) − 1)/4⌋ + j − Q`. -/
def PhiBitlen (m Q : Nat) (v : InvVertex) : Int :=
  (((Nat.size (v.c % 3 ^ (22 * m + 2 + v.j)) - 1) / 4 : ℕ) : Int)
    + (v.j : Int) - (Q : Int)

/-- **The PhiBitlen κ-edge inequality** (start-independent). -/
theorem phiBitlen_edge (m Q : Nat) :
    ∀ v v' κ, v.j ≤ Q → v'.j ≤ Q →
      InvKappaPreciseEdge (22 * m + 2) v v' κ →
      PhiBitlen m Q v ≤ κ + PhiBitlen m Q v' := by
  intro v v' κ _ _ hedge
  rcases hedge with ⟨ω, he, hκ⟩ | ⟨ω, he, hτ, hκ⟩ | ⟨ω, he, hτ, hκ⟩
  · -- one-edge, κ = +1
    have hj : v'.j = v.j := he.1
    have hb : 1 ≤ Nat.size (v'.c % 3 ^ (22 * m + 2 + v.j)) := by
      have hne : v'.c % 3 ^ (22 * m + 2 + v.j) ≠ 0 :=
        canon_ne_zero_of_InX he.2.1 (by omega)
      have := Nat.size_pos.mpr (Nat.pos_of_ne_zero hne)
      omega
    have hsize := oneEdge_size_le (by omega) he
    unfold PhiBitlen
    rw [hj, hκ]
    omega
  · -- zero-edge, τ = 1, κ = −1
    have hj : v'.j = v.j + 1 := he.1
    have hsize := zeroEdge_size_le (by omega) he
    rw [hτ] at hsize
    unfold PhiBitlen
    rw [hj, hκ]
    rw [hj] at hsize
    omega
  · -- zero-edge, τ ≥ 2, κ = 0
    have hj : v'.j = v.j + 1 := he.1
    have hb : 1 ≤ Nat.size (v'.c % 3 ^ (22 * m + 2 + v'.j)) := by
      have hne : v'.c % 3 ^ (22 * m + 2 + v'.j) ≠ 0 :=
        canon_ne_zero_of_InX he.2.1 (by omega)
      have := Nat.size_pos.mpr (Nat.pos_of_ne_zero hne)
      omega
    have hsize := zeroEdge_size_le (by omega) he
    have hτ4 : tau v'.c ≤ 4 := tau_le_four v'.c
    unfold PhiBitlen
    rw [hκ]
    rw [hj] at hsize hb ⊢
    omega

/-- **The PhiBitlen goal bound** (start-independent). -/
theorem phiBitlen_goal (m Q : Nat) :
    ∀ v, InvVertex.IsGoal v (22 * m + 2) → v.j ≤ Q → PhiBitlen m Q v ≤ 0 := by
  intro v hgoal hjQ
  have hM : 1 < 3 ^ (22 * m + 2 + v.j) := by
    have h31 : (3 : ℕ) ^ 1 ≤ 3 ^ (22 * m + 2 + v.j) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (3 : ℕ) ^ 1 = 3 := pow_one 3
    omega
  have h1 : v.c % 3 ^ (22 * m + 2 + v.j) = 1 := by
    have h : v.c % 3 ^ (22 * m + 2 + v.j) = 1 % 3 ^ (22 * m + 2 + v.j) := hgoal
    rwa [Nat.mod_eq_of_lt hM] at h
  unfold PhiBitlen
  rw [h1, Nat.size_one]
  omega

/-- **The closed-form bounded κ barrier.**  Whenever the start has enough bits
(`4(m+Q)+1 ≤ size(aS202 mod 3^(22m+2))`), the bounded κ-precise barrier holds — with no
search, no certificate table, no `native_decide`. -/
theorem kappa_bounded_barrier_bitlen (m Q : Nat)
    (h0 : 4 * (m + Q) + 1 ≤ Nat.size (aS202 % 3 ^ (22 * m + 2))) :
    S202_kappa_precise_barrier_bounded m Q := by
  apply S202_kappa_precise_barrier_bounded_from_potential m Q (PhiBitlen m Q)
  · exact phiBitlen_edge m Q
  · exact phiBitlen_goal m Q
  · -- the start bound
    unfold PhiBitlen
    have hj0 : (InvStart m).j = 0 := rfl
    have hc : (InvStart m).c = aS202 % 3 ^ (22 * m + 2) := rfl
    rw [hj0, hc]
    have hmm : aS202 % 3 ^ (22 * m + 2) % 3 ^ (22 * m + 2 + 0)
        = aS202 % 3 ^ (22 * m + 2) := by
      rw [Nat.add_zero, Nat.mod_mod_of_dvd _ (dvd_refl _)]
    rw [hmm]
    omega

/-- **The generic-start closed-form barrier** — the socket for the faithful per-`m` tower
(the Caveat-C migration): every κ-precise path from ANY vertex `v₀` with enough bits
(`4(m+Q)+1 ≤ size(canon v₀) + 4·v₀.j`) to a goal in the `Q`-slice has κ-cost `≥ m`.
The current `InvStart` instantiates it with 35 bits at `j = 0`; a faithful `aS202_at m`
start (B₀ ≈ 34.9·m bits) would unlock `Q ≲ 7.7m`. -/
theorem kappa_bounded_barrier_bitlen_from (m Q : Nat) (v₀ : InvVertex)
    (h0 : 4 * (m + Q) + 1 ≤ Nat.size (v₀.c % 3 ^ (22 * m + 2 + v₀.j)) + 4 * v₀.j) :
    ∀ {goal : InvVertex} {κ : Int} {vs : List InvVertex},
      InvVertex.IsGoal goal (22 * m + 2) → goal.j ≤ Q →
      WPath (InvKappaPreciseEdge (22 * m + 2)) v₀ goal κ vs →
      (m : Int) ≤ κ := by
  intro goal κ vs hg hgQ hpath
  have hmono := WPath_kappa_j_monotone hpath
  have hv₀Q : v₀.j ≤ Q := le_trans hmono.1 hgQ
  have hvs : ∀ x ∈ vs, x.j ≤ Q := fun x hx => le_trans (hmono.2 x hx) hgQ
  have htele := WPath_kappa_weight_ge_potential_bounded (PhiBitlen m Q)
    (phiBitlen_edge m Q) hv₀Q hgQ hvs hpath
  have hgoal := phiBitlen_goal m Q goal hg hgQ
  have hstart : (m : Int) ≤ PhiBitlen m Q v₀ := by
    unfold PhiBitlen
    omega
  linarith

/-- **Uniform closed-form corollary** (current Caveat-C start, 35 bits): the bounded κ
barrier holds for ALL `m ≥ 1`, `Q` with `m + Q ≤ 8` — covering `m=2, Q≤6`; `m=3, Q≤5`;
…; `m=7, Q≤1` in one stroke, each previously requiring its own certificate. -/
theorem kappa_barrier_of_sum_le_eight (m Q : Nat) (hm : 1 ≤ m) (hmQ : m + Q ≤ 8) :
    S202_kappa_precise_barrier_bounded m Q := by
  apply kappa_bounded_barrier_bitlen m Q
  have hlt : aS202 < 3 ^ (22 * m + 2) := by
    rw [aS202_decomp]
    have h23 : (3 : ℕ) ^ 23 ≤ 3 ^ (22 * m + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 + 3 ^ 22 < 3 ^ 23 := by norm_num
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have h32 : (2 : ℕ) ^ 32 ≤ aS202 := by
    rw [aS202_decomp]
    norm_num
  have := Nat.lt_size.mpr h32
  omega

/-- **Headline instance**: the closed-form barrier at `m = 1` up to `Q = 7` — subsuming
the κ-range of the per-instance certificates (`Cert_m1_Q*_kappa`, `Q ≤ 3`) and the
engine's exploration (`Q ≤ 5`), and extending it to `Q = 6, 7`, with an elementary
proof.  (`size(aS202) = 35`: `2³⁴ ≤ 1 + 3²² < 2³⁵`.) -/
theorem kappa_barrier_m1_Q7 : S202_kappa_precise_barrier_bounded 1 7 := by
  apply kappa_bounded_barrier_bitlen 1 7
  -- 33 ≤ size(aS202 % 3^24) = size(1 + 3^22) = 35
  have hred : aS202 % 3 ^ (22 * 1 + 2) = 1 + 3 ^ 22 := by
    rw [aS202_decomp]
    exact Nat.mod_eq_of_lt (by norm_num)
  rw [hred]
  have h32 : (2 : ℕ) ^ 32 ≤ 1 + 3 ^ 22 := by norm_num
  have := Nat.lt_size.mpr h32
  omega

end CollatzLean4.Admissible
