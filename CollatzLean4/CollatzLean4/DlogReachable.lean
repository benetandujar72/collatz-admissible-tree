/-
Copyright (c) 2026 Benet Andújar Guardado.

S239 — Wall-B Tier-2 core: the discrete-log function and the reachable-residue object.

The pivot verdict (formalized via DiscreteLog) reduced the slope-barrier residual to a
REACHABILITY question on discrete-log residues, NOT equidistribution/discrepancy. This
module provides the concrete Lean carriers:
  * `dlog` — the discrete log base 2 mod 3^k (every unit is `2^(dlog c)`), packaging
    `exists_two_pow_eq_of_isUnit`.
  * `ReachableDlog m` — the set of dlog residues of c-coordinates reachable from
    `InvStart m` along admissible inverse paths. This is the precise, non-circular Lean
    object the residual reduces to (the genuine OPEN CORE, Tier-2 structural).
0 sorry / 0 ad-hoc axiom.
-/

import CollatzLean4.DiscreteLog

namespace CollatzLean4.Admissible

open Classical

/-! ### The discrete-log function -/

/-- Discrete log base 2 mod 3^k: a chosen exponent `t` with `2^t = c` (exists for units,
since 2 is a primitive root). Total (`0` off the units), noncomputable. -/
noncomputable def dlog (k : ℕ) (c : ZMod (3 ^ k)) : ℕ :=
  if h : ∃ t : ℕ, (2 : ZMod (3 ^ k)) ^ t = c then h.choose else 0

/-- Defining property: `2^(dlog c) = c` for every unit `c` (k ≥ 1). -/
theorem two_pow_dlog (k : ℕ) (hk : 1 ≤ k) {c : ZMod (3 ^ k)} (hc : IsUnit c) :
    (2 : ZMod (3 ^ k)) ^ (dlog k c) = c := by
  have h : ∃ t : ℕ, (2 : ZMod (3 ^ k)) ^ t = c := exists_two_pow_eq_of_isUnit k hk hc
  unfold dlog
  rw [dif_pos h]
  exact h.choose_spec

/-- `2 : ZMod 3^k` is of finite order (its order is `2·3^{k-1} > 0`). -/
theorem isOfFinOrder_two (k : ℕ) (hk : 1 ≤ k) : IsOfFinOrder (2 : ZMod (3 ^ k)) := by
  rw [← orderOf_pos_iff, orderOf_two_zmod_three_pow k hk]; positivity

/-- Injectivity of `t ↦ 2^t` mod the order: `2^n = 2^m ⟺ n ≡ m (mod 2·3^{k-1})`. -/
theorem two_pow_eq_iff_modEq (k : ℕ) (hk : 1 ≤ k) {n m : ℕ} :
    (2 : ZMod (3 ^ k)) ^ n = (2 : ZMod (3 ^ k)) ^ m ↔ n ≡ m [MOD 2 * 3 ^ (k - 1)] := by
  rw [(isOfFinOrder_two k hk).pow_eq_pow_iff_modEq, orderOf_two_zmod_three_pow k hk]

/-- **Wall-B reformulation (dlog form).** For a unit `c`,
`2^τ = c ⟺ τ ≡ dlog(c) (mod 2·3^{k-1})`. -/
theorem two_pow_eq_iff_dlog (k : ℕ) (hk : 1 ≤ k) {c : ZMod (3 ^ k)} (hc : IsUnit c) (τ : ℕ) :
    (2 : ZMod (3 ^ k)) ^ τ = c ↔ τ ≡ dlog k c [MOD 2 * 3 ^ (k - 1)] := by
  have hd : (2 : ZMod (3 ^ k)) ^ (dlog k c) = c := two_pow_dlog k hk hc
  nth_rewrite 1 [← hd]
  exact two_pow_eq_iff_modEq k hk

/-! ### Reachability in the inverse cylinder graph -/

/-- A vertex is reachable from `InvStart m` via an admissible inverse path. -/
def InvReachable (m : ℕ) (v : InvVertex) : Prop :=
  ∃ (w : Int) (vs : List InvVertex),
    WPath (InvEdge (22 * m + 2)) (InvStart m) v w vs

/-- The start vertex is reachable (the empty path). -/
theorem invReachable_start (m : ℕ) : InvReachable m (InvStart m) :=
  ⟨0, [], rfl, rfl⟩

/-- **Extend a weighted path by one edge at the end (snoc).** Generic over any graph. -/
theorem WPath_snoc {V : Type} {edge : V → V → Int → Prop}
    {t t' : V} {ω : Int} (he : edge t t' ω) :
    ∀ {s : V} {w : Int} {vs : List V},
      WPath edge s t w vs → WPath edge s t' (w + ω) (vs ++ [t']) := by
  intro s w vs h
  induction vs generalizing s w with
  | nil =>
      simp only [WPath] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ω, 0, he, ⟨rfl, rfl⟩, by ring⟩
  | cons v vs ih =>
      simp only [WPath] at h
      obtain ⟨ω₁, ω₂, hsv, hrest, rfl⟩ := h
      exact ⟨ω₁, ω₂ + ω, hsv, ih hrest, by ring⟩

/-- **Reachability is closed under admissible edges.** If `v` is reachable from
`InvStart m` and there is an inverse edge `v → v'`, then `v'` is reachable. This is the
inductive backbone for reasoning about the reachable set. -/
theorem invReachable_step (m : ℕ) {v v' : InvVertex} {ω : Int}
    (hv : InvReachable m v) (he : InvEdge (22 * m + 2) v v' ω) :
    InvReachable m v' := by
  obtain ⟨w, vs, hpath⟩ := hv
  exact ⟨w + ω, vs ++ [v'], WPath_snoc he hpath⟩

/-- **Induction principle for reachability.** To prove a property `P` of every vertex
reachable from `InvStart m`, it suffices to show `P (InvStart m)` and that `P` is preserved
along every admissible edge. The fundamental tool for reasoning about the reachable set. -/
theorem InvReachable_induction (m : ℕ) {P : InvVertex → Prop}
    (hstart : P (InvStart m))
    (hstep : ∀ v v' ω, P v → InvEdge (22 * m + 2) v v' ω → P v')
    {v : InvVertex} (hv : InvReachable m v) : P v := by
  obtain ⟨w, vs, hpath⟩ := hv
  have H : ∀ (vs : List InvVertex) (s : InvVertex) (w : Int),
      P s → WPath (InvEdge (22 * m + 2)) s v w vs → P v := by
    intro vs
    induction vs with
    | nil =>
        intro s w hs hpath
        simp only [WPath] at hpath
        obtain ⟨rfl, _⟩ := hpath
        exact hs
    | cons v₁ rest ih =>
        intro s w hs hpath
        simp only [WPath] at hpath
        obtain ⟨ω₁, ω₂, hedge, hrest, _⟩ := hpath
        exact ih v₁ ω₂ (hstep s v₁ ω₁ hs hedge) hrest
  exact H vs (InvStart m) w hstart hpath

/-- The start vertex's c-coordinate is admissible (`aS202 ≡ 1 mod 9`). -/
theorem invStart_InX (m : ℕ) : InX (InvStart m).c := by
  show InX (aS202 % 3 ^ (22 * m + 2))
  have h9 : (9 : ℕ) ∣ 3 ^ (22 * m + 2) := by
    have h : (3 : ℕ) ^ 2 ∣ 3 ^ (22 * m + 2) := pow_dvd_pow 3 (by omega)
    simpa using h
  have hmod : (aS202 % 3 ^ (22 * m + 2)) % 9 = aS202 % 9 := Nat.mod_mod_of_dvd aS202 h9
  unfold InX
  rw [hmod, S206_a_mod9]
  decide

/-- **Every reachable vertex has an admissible c-coordinate.** Proven by reachability
induction: the start is admissible (`invStart_InX`) and every inverse edge requires its
target admissible. Hence the c-residue is always a unit mod 3^k, so `dlog` is defined on
all of `ReachableDlog` — the reachable-residue object is well-formed, not vacuous. -/
theorem invReachable_InX (m : ℕ) {v : InvVertex} (hv : InvReachable m v) : InX v.c := by
  refine InvReachable_induction m (P := fun v => InX v.c) (invStart_InX m) ?_ hv
  intro a b ω _ hedge
  rcases hedge with h | h
  · exact h.2.1
  · exact h.2.1

/-- **One-edge discrete-log shift (the structural content of the reachable set).** Along a
one-edge `v → v'` (same j-level), the discrete log shifts by exactly the edge weight `τ`:
`dlog(v.c) ≡ τ + dlog(v'.c) (mod 2·3^{R+j-1})`, where `τ = tau v'.c`. So one-edges
translate `dlog` by a known amount — `ReachableDlog` is generated from the start residue by
these explicit shifts (a τ-labelled orbit), not an opaque set. This is the concrete handle
on the Wall-B open core. -/
theorem oneEdge_dlog_shift (m : ℕ) {v v' : InvVertex} {ω : Int}
    (hv : InX v.c) (he : InvEdgeOne (22 * m + 2) v v' ω) :
    dlog (22 * m + 2 + v.j) ((v.c : ZMod (3 ^ (22 * m + 2 + v.j))))
      ≡ tau v'.c + dlog (22 * m + 2 + v.j) ((v'.c : ZMod (3 ^ (22 * m + 2 + v.j))))
        [MOD 2 * 3 ^ (22 * m + 2 + v.j - 1)] := by
  obtain ⟨hj, hX', hcong, hτ⟩ := he
  set k := 22 * m + 2 + v.j with hk_def
  have hk : 1 ≤ k := by omega
  clear_value k
  have hunit : IsUnit ((v.c : ZMod (3 ^ k))) :=
    (ZMod.isUnit_iff_coprime v.c (3 ^ k)).mpr (InX_coprime_three_pow hv k)
  have hunit' : IsUnit ((v'.c : ZMod (3 ^ k))) :=
    (ZMod.isUnit_iff_coprime v'.c (3 ^ k)).mpr (InX_coprime_three_pow hX' k)
  have hcu : (2 : ZMod (3 ^ k)) ^ (dlog k ((v.c : ZMod (3 ^ k)))) = (v.c : ZMod (3 ^ k)) :=
    two_pow_dlog k hk hunit
  have hcu' : (2 : ZMod (3 ^ k)) ^ (dlog k ((v'.c : ZMod (3 ^ k)))) = (v'.c : ZMod (3 ^ k)) :=
    two_pow_dlog k hk hunit'
  have hedge : ((v.c : ZMod (3 ^ k))) = 2 ^ (tau v'.c) * ((v'.c : ZMod (3 ^ k))) := by
    have h1 : (v.c : ZMod (3 ^ k)) = ((2 ^ (tau v'.c) * v'.c : ℕ) : ZMod (3 ^ k)) := by
      rw [ZMod.natCast_eq_natCast_iff]; exact hcong
    rw [h1]; push_cast; ring
  have key : (2 : ZMod (3 ^ k)) ^ (dlog k ((v.c : ZMod (3 ^ k))))
      = (2 : ZMod (3 ^ k)) ^ (tau v'.c + dlog k ((v'.c : ZMod (3 ^ k)))) := by
    rw [pow_add, hcu, hedge, hcu']
  exact (two_pow_eq_iff_modEq k hk).mp key

/-- **Zero-edge discrete-log shift.** Along a zero-edge `v → v'` (`j ↦ j+1`, modulus lifts
to `3^{R+j+1}`), the source residue transforms to `3·v.c+1` (a unit, `≡ 1 mod 3`) and:
`dlog(3·v.c+1) ≡ τ + dlog(v'.c) (mod 2·3^{R+j})`, at the v'-level modulus. Together with
`oneEdge_dlog_shift` this is the FULL one-step generation rule for `ReachableDlog`: both
edge types translate `dlog` by the weight `τ` (the zero-edge first applying the affine
`x ↦ 3x+1` and re-indexing to the finer modulus). The remaining hard piece — relating
`dlog(3·v.c+1)` at level `j+1` back to `dlog(v.c)` at level `j` (the 3-multiplication ×
modulus-lift interaction) — is the genuine open arithmetic of the orbit. -/
theorem zeroEdge_dlog_shift (m : ℕ) {v v' : InvVertex} {ω : Int}
    (he : InvEdgeZero (22 * m + 2) v v' ω) :
    dlog (22 * m + 2 + v'.j) ((3 * v.c + 1 : ℕ) : ZMod (3 ^ (22 * m + 2 + v'.j)))
      ≡ tau v'.c + dlog (22 * m + 2 + v'.j) ((v'.c : ZMod (3 ^ (22 * m + 2 + v'.j))))
        [MOD 2 * 3 ^ (22 * m + 2 + v'.j - 1)] := by
  obtain ⟨hj, hX', hcong, hτ⟩ := he
  set k := 22 * m + 2 + v'.j with hk_def
  have hk : 1 ≤ k := by omega
  clear_value k
  have hcop : Nat.Coprime (3 * v.c + 1) (3 ^ k) := by
    have h3 : ¬ (3 : ℕ) ∣ (3 * v.c + 1) := by omega
    exact ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm.pow_right k
  have hunit : IsUnit (((3 * v.c + 1 : ℕ) : ZMod (3 ^ k))) :=
    (ZMod.isUnit_iff_coprime (3 * v.c + 1) (3 ^ k)).mpr hcop
  have hunit' : IsUnit ((v'.c : ZMod (3 ^ k))) :=
    (ZMod.isUnit_iff_coprime v'.c (3 ^ k)).mpr (InX_coprime_three_pow hX' k)
  have hcu : (2 : ZMod (3 ^ k)) ^ (dlog k (((3 * v.c + 1 : ℕ) : ZMod (3 ^ k))))
      = ((3 * v.c + 1 : ℕ) : ZMod (3 ^ k)) := two_pow_dlog k hk hunit
  have hcu' : (2 : ZMod (3 ^ k)) ^ (dlog k ((v'.c : ZMod (3 ^ k)))) = (v'.c : ZMod (3 ^ k)) :=
    two_pow_dlog k hk hunit'
  have hedge : (((3 * v.c + 1 : ℕ) : ZMod (3 ^ k))) = 2 ^ (tau v'.c) * ((v'.c : ZMod (3 ^ k))) := by
    have h1 : ((3 * v.c + 1 : ℕ) : ZMod (3 ^ k)) = ((2 ^ (tau v'.c) * v'.c : ℕ) : ZMod (3 ^ k)) := by
      rw [ZMod.natCast_eq_natCast_iff]; exact hcong
    rw [h1]; push_cast; ring
  have key : (2 : ZMod (3 ^ k)) ^ (dlog k (((3 * v.c + 1 : ℕ) : ZMod (3 ^ k))))
      = (2 : ZMod (3 ^ k)) ^ (tau v'.c + dlog k ((v'.c : ZMod (3 ^ k)))) := by
    rw [pow_add, hcu, hedge, hcu']
  exact (two_pow_eq_iff_modEq k hk).mp key

/-- **Cross-level dlog compatibility (the discrete-log tower).** For a residue coprime to 3,
the discrete log at the coarser level `j` is that at the finer level `j+1` reduced mod the
coarser order: `dlog_j(c) ≡ dlog_{j+1}(c) (mod 2·3^{j-1})`. (The projection
`ZMod 3^{j+1} → ZMod 3^j` is a ring hom fixing 2.) This is how a zero-edge's finer-level dlog
relates down the tower — half of the 3x+1 reindexing; the other half (the affine `x↦3x+1`
itself in dlog coordinates) is the open core. -/
theorem dlog_reduce (c j : ℕ) (hj : 1 ≤ j) (hco : Nat.Coprime c 3) :
    dlog j ((c : ZMod (3 ^ j)))
      ≡ dlog (j + 1) ((c : ZMod (3 ^ (j + 1)))) [MOD 2 * 3 ^ (j - 1)] := by
  have hunit_j : IsUnit ((c : ZMod (3 ^ j))) :=
    (ZMod.isUnit_iff_coprime c (3 ^ j)).mpr (hco.pow_right j)
  have hunit_j1 : IsUnit ((c : ZMod (3 ^ (j + 1)))) :=
    (ZMod.isUnit_iff_coprime c (3 ^ (j + 1))).mpr (hco.pow_right (j + 1))
  have hd1 := two_pow_dlog (j + 1) (by omega) hunit_j1
  have hmod1 : (2 : ℕ) ^ (dlog (j + 1) ((c : ZMod (3 ^ (j + 1))))) ≡ c [MOD 3 ^ (j + 1)] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    rw [hd1]
  have hdvd : 3 ^ j ∣ 3 ^ (j + 1) := pow_dvd_pow 3 (Nat.le_succ j)
  have hmodj : (2 : ℕ) ^ (dlog (j + 1) ((c : ZMod (3 ^ (j + 1))))) ≡ c [MOD 3 ^ j] :=
    Nat.ModEq.of_dvd hdvd hmod1
  have hd1j : (2 : ZMod (3 ^ j)) ^ (dlog (j + 1) ((c : ZMod (3 ^ (j + 1))))) = (c : ZMod (3 ^ j)) := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodj
    push_cast at h
    exact h
  have hd2j : (2 : ZMod (3 ^ j)) ^ (dlog j ((c : ZMod (3 ^ j)))) = (c : ZMod (3 ^ j)) :=
    two_pow_dlog j hj hunit_j
  exact (two_pow_eq_iff_modEq j hj).mp (by rw [hd2j, hd1j])

/-! ### The sign (ℤ/2 Teichmüller) part of dlog is CLOSED FORM

A cross-disciplinary (p-adic) discovery, numerically verified then formalized: because
`2 ≡ −1 (mod 3)`, the order-2 component of the discrete log is just the quadratic character
`c ↦ [c ≡ 2 mod 3]`. So the `affineDlogJump`'s 2-adic⊗3-adic coupling lives ENTIRELY in this
sign bit; the `3^{k-1}`-component is the *analytic* 3-adic log series `log₃(1+3x)`. -/

/-- `2^t mod 3` cycles with period 2: `= 1` if `t` even, `= 2` if `t` odd. -/
theorem two_pow_mod_three (t : ℕ) : (2 : ℕ) ^ t % 3 = if t % 2 = 0 then 1 else 2 := by
  induction t with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      by_cases h : n % 2 = 0
      · have h1 : (n + 1) % 2 ≠ 0 := by omega
        rw [if_pos h, if_neg h1]
      · have h1 : (n + 1) % 2 = 0 := by omega
        rw [if_neg h, if_pos h1]

/-- **The sign part of dlog is closed-form.** For a unit residue `c` (coprime to 3), the parity
of the discrete log is the quadratic character: `dlog(c) % 2 = [c ≡ 2 (mod 3)]`. (Since
`2 ≡ −1 mod 3`, `2^{dlog c} ≡ c` reduces mod 3 to `(−1)^{dlog c} = c mod 3`.) -/
theorem dlog_mod_two (k c : ℕ) (hk : 1 ≤ k) (hco : Nat.Coprime c 3) :
    dlog k ((c : ZMod (3 ^ k))) % 2 = if c % 3 = 2 then 1 else 0 := by
  have hunit : IsUnit ((c : ZMod (3 ^ k))) :=
    (ZMod.isUnit_iff_coprime c (3 ^ k)).mpr (hco.pow_right k)
  have hd := two_pow_dlog k hk hunit
  have hmodk : (2 : ℕ) ^ (dlog k ((c : ZMod (3 ^ k)))) ≡ c [MOD 3 ^ k] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp; push_cast; rw [hd]
  have hdvd : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hmod3' : (2 : ℕ) ^ (dlog k ((c : ZMod (3 ^ k)))) % 3 = c % 3 :=
    Nat.ModEq.of_dvd hdvd hmodk
  rw [two_pow_mod_three] at hmod3'
  have hc3 : c % 3 ≠ 0 := by
    have hnd : ¬ (3 : ℕ) ∣ c := (Nat.prime_three.coprime_iff_not_dvd).mp hco.symm
    omega
  have hlt : dlog k ((c : ZMod (3 ^ k))) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases hp : dlog k ((c : ZMod (3 ^ k))) % 2 = 0
  · rw [if_pos hp] at hmod3'
    rw [hp, if_neg (show c % 3 ≠ 2 by omega)]
  · rw [if_neg hp] at hmod3'
    rw [if_pos (show c % 3 = 2 by omega)]; omega

/-- The discrete log of `3c+1` is always EVEN (since `3c+1 ≡ 1 mod 3`). Hence in
`affineDlogJump = dlog(3c+1) − dlog(c)` the first term contributes no sign, and the whole
jump's parity is `[c ≡ 2 mod 3]` — a closed form, the entire coupling reduced to one bit. -/
theorem dlog_three_c_add_one_even (c j : ℕ) :
    dlog (j + 1) ((3 * c + 1 : ℕ) : ZMod (3 ^ (j + 1))) % 2 = 0 := by
  have hco : Nat.Coprime (3 * c + 1) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr (by omega : ¬ (3 : ℕ) ∣ (3 * c + 1))).symm
  rw [dlog_mod_two (j + 1) (3 * c + 1) (by omega) hco, if_neg (by omega : ¬ (3 * c + 1) % 3 = 2)]

/-! ### dlog is a LOGARITHM (group homomorphism)

The structural essence behind "the 3-adic part is analytic": `dlog : units → ℤ/(2·3^{k-1})` is a
group homomorphism (`dlog(ab) ≡ dlog a + dlog b`). This is exactly what makes the affine jump a
single `dlog` of the ratio `(3c+1)/c` and what turns the zero-edge "open arithmetic" into the
`log₃` homomorphism — the analytic structure, proven directly from the order law (no series). -/

/-- **`dlog` is additive (logarithm law).** For units `a,b`,
`dlog(a·b) ≡ dlog a + dlog b (mod 2·3^{k-1})`. -/
theorem dlog_mul (k : ℕ) (hk : 1 ≤ k) {a b : ZMod (3 ^ k)} (ha : IsUnit a) (hb : IsUnit b) :
    dlog k (a * b) ≡ dlog k a + dlog k b [MOD 2 * 3 ^ (k - 1)] := by
  have h1 : (2 : ZMod (3 ^ k)) ^ (dlog k (a * b)) = a * b := two_pow_dlog k hk (ha.mul hb)
  have h2 : (2 : ZMod (3 ^ k)) ^ (dlog k a + dlog k b) = a * b := by
    rw [pow_add, two_pow_dlog k hk ha, two_pow_dlog k hk hb]
  exact (two_pow_eq_iff_modEq k hk).mp (h1.trans h2.symm)

/-- `dlog 1 ≡ 0`. -/
theorem dlog_one (k : ℕ) (hk : 1 ≤ k) :
    dlog k (1 : ZMod (3 ^ k)) ≡ 0 [MOD 2 * 3 ^ (k - 1)] := by
  have h1 : (2 : ZMod (3 ^ k)) ^ (dlog k (1 : ZMod (3 ^ k))) = 1 :=
    two_pow_dlog k hk isUnit_one
  exact (two_pow_eq_iff_modEq k hk).mp (h1.trans (pow_zero _).symm)

/-- **`dlog` of a power: `dlog(aⁿ) ≡ n·dlog a`.** Completes the homomorphism package. -/
theorem dlog_pow (k : ℕ) (hk : 1 ≤ k) {a : ZMod (3 ^ k)} (ha : IsUnit a) (n : ℕ) :
    dlog k (a ^ n) ≡ n * dlog k a [MOD 2 * 3 ^ (k - 1)] := by
  have h1 : (2 : ZMod (3 ^ k)) ^ (dlog k (a ^ n)) = a ^ n :=
    two_pow_dlog k hk (ha.pow n)
  have h2 : (2 : ZMod (3 ^ k)) ^ (n * dlog k a) = a ^ n := by
    rw [mul_comm, pow_mul, two_pow_dlog k hk ha]
  exact (two_pow_eq_iff_modEq k hk).mp (h1.trans h2.symm)

/-! ### The open arithmetic core: the affine `x ↦ 3x+1` in dlog coordinates -/

/-- **The affine dlog jump.** `affineDlogJump c j` is the change in discrete log at level `j+1`
induced by the Collatz affine map `x ↦ 3x+1`: `dlog_{j+1}(3c+1) − dlog_{j+1}(c)`.

**Refined (2026-05-30, via a p-adic cross-check, partially formalized).** It does NOT lack all
structure. Splitting `(ℤ/3^{j+1})^× ≅ ℤ/2 × ℤ/3^j` (since `2 ≡ −1 mod 3`):
  * the **ℤ/2 sign (Teichmüller) part is CLOSED FORM** — `dlog_three_c_add_one_even` +
    `dlog_mod_two` give jump-parity `= [c ≡ 2 mod 3]`;
  * the **ℤ/3^j principal part is the ANALYTIC 3-adic log series** `log₃(1+3x) =
    Σ (−1)^{n+1}(3x)^n/n` (convergent, term-controlled; numerically verified exact against this
    `dlog` for k=2..6) — NOT opaque, an explicit truncatable series.
So the 2-adic⊗3-adic coupling of `affineDlogJump` is localized ENTIRELY to the one-bit sign
character; the 3-adic part is tame/analytic. What remains genuinely open is the SIMULTANEOUS
control of the sign-walk and the log₃-orbit along admissible κ-paths (the constrained-reachability
question — Furstenberg-TOPOLOGICAL-flavoured, not the measure conjecture). Next formal step
(scoped): a truncated-`log₃` def + the principal-part identity. -/
noncomputable def affineDlogJump (c j : ℕ) : ℤ :=
  (dlog (j + 1) ((3 * c + 1 : ℕ) : ZMod (3 ^ (j + 1))) : ℤ)
    - (dlog (j + 1) ((c : ℕ) : ZMod (3 ^ (j + 1))) : ℤ)

/-! ### The reachable discrete-log residue set (Wall-B Tier-2 carrier) -/

/-- **The reachable discrete-log residue set.** The discrete logs of the c-coordinates of
vertices reachable from `InvStart m`, each taken mod its own cylinder modulus
`3^(22m+2+j)`. This is the concrete object the slope-barrier residual reduces to. -/
def ReachableDlog (m : ℕ) : Set ℕ :=
  { d | ∃ v : InvVertex, InvReachable m v ∧
      IsUnit ((v.c : ZMod (3 ^ (22 * m + 2 + v.j)))) ∧
      dlog (22 * m + 2 + v.j) ((v.c : ZMod (3 ^ (22 * m + 2 + v.j)))) = d }

/-! ### OPEN CORE (Wall-B, Tier-2 structural)

The slope-barrier residual `FirstMPrecisionSuffixPositive m Q` reduces — via the dlog
reformulation (`exists_two_pow_eq_of_isUnit` + `three_pow_dvd_sub_iff_modEq`:
`ν₃(c − 2^τ) ≥ j ⟺ c ≡ 2^τ (mod 3^j) ⟺ dlog(c) ≡ τ (mod 2·3^{j-1})`) — to a REACHABILITY
question on `ReachableDlog m`: whether the "trap" residues (`dlog ≡ τ` but `≢ 0` at the
critical depth ≈ 3^21) are always reachable, or an intermediate m-precise vertex with a
positive κ₂ tail is forced.

This is a precise, non-circular question about the concrete set `ReachableDlog m`. It is
genuinely OPEN — the reachable set is the inverse dynamics' combinatorics. Crucially it is
NOT an equidistribution/discrepancy statement (which would be Tier-3 / possibly-open
Furstenberg ×2×3 territory); it is structural reachability — Tier-2. The pivot thereby
reclassified Wall B from possibly-open to a more tractable structural problem, and this
module gives the open core a concrete Lean home. -/

end CollatzLean4.Admissible
