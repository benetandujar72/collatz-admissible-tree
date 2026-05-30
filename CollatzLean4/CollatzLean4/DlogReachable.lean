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
