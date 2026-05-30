/-
**R2 projection functor for the `KappaPathSplit` reduction.**

`KappaPathSplit m Q` (the single open core of the uniform slope-barrier route,
committed in `UniformBarrier.lean`) splits every κ-precise path from the
`(m+1)`-level start to an `(m+1)`-goal into a prefix of κ-cost ≥ `m` and a suffix
of κ-cost ≥ `1`. The intended proof has two halves:

  * **R1** (suffix κ₂ ≥ 1) — the outermost `wS202` block forces a net one-edge;
  * **R2** (prefix κ₁ ≥ m) — the inner path, *projected from precision `22(m+1)+2`
    down to `22m+2`*, carries the m-level barrier (the committed induction
    hypothesis `S202_kappa_precise_barrier_bounded m Q`).

R2 needs a **precision-reduction map** turning a `(m+1)`-level κ-path into a
genuine `m`-level κ-path, so that the IH barrier can be applied. This module
supplies that map and proves it is a κ-preserving functor on the κ-precise
inverse graph — the single unconditionally-true, `native_decide`-free brick in
this neighbourhood.

## What is proved here (all unconditional, 0 `sorry`)

  * `projπ m v := ⟨v.j, v.c % 3^(22m+2+v.j)⟩` — the precision-reduction map.
  * `InvKappaPreciseEdge_projectDown` — **the core brick**: `projπ` sends a
    level-`(m+1)` κ-precise edge to a level-`m` κ-precise edge with the *same* κ.
  * `WPath_projectDown` — the path-level lift (functoriality): a level-`(m+1)`
    κ-path maps to a level-`m` κ-path of the same total κ and projected vertices.
  * `IsGoal_projectDown` — goals descend: a level-`(m+1)` goal projects to a
    level-`m` goal.
  * `projπ_InvStart` — `projπ` fixes the start vertex: `projπ m (InvStart (m+1))
    = InvStart m` (an *accident of the shared constant* `aS202`; see the honest
    caveat below).
  * `KappaProjectsDown` (a named `Prop`) + `kappaProjectsDown_holds` — packages
    R2's precision-tower step as a discharged hypothesis, removing it from the
    open set.

## The honest companion (why this does NOT close `KappaPathSplit`)

  * `IsGoal_projectDown_not_reflects` — **the converse of `IsGoal_projectDown`
    fails**: there is a vertex whose projection is a level-`m` goal while the
    vertex itself is *not* a level-`(m+1)` goal. Hence `projπ` is many-to-one and
    cannot, by itself, transport the *fine* `(m+1)`-prefix κ-bound that R2 needs
    — the projected prefix lands at a *projected* goal, but recovering the
    `(m+1)`-level split point requires information `projπ` has thrown away. This
    is the formal reason R2 reduces to, but does not discharge, the split.

  * **Caveat C (`InvStart` is the wrong start for `m ≥ 2`).** `projπ_InvStart`
    holds only because `InvStart m := ⟨0, aS202 % 3^(22m+2)⟩` reuses the single
    low-precision constant `aS202 = 1 + 3^22`. By `aS202_at_2_ne_aS202_mod_3_46`
    (AS202Lift.lean) that constant is the *wrong* S202 fixed-point cylinder for
    `m ≥ 2`, so any `m ≥ 2` use of the IH barrier on the projected prefix is on
    sand until `InvStart` migrates to the coherent tower `aS202_at m`. This is
    flagged, not silently assumed.

## Residual open content of `KappaPathSplit`

After this brick, `KappaPathSplit m Q` reduces to: *exhibit a split point `mid`
on the level-`(m+1)` path that is simultaneously the end of the outermost-`wS202`
image (R1) AND projects onto an m-level goal whose prefix realises the IH barrier
(R2)*. The functor here discharges "the projected prefix is a real level-`m`
κ-path"; the non-constructibility of `mid` (no canonical cut, by
`kappa_no_canonical_depth_cut`) and the `InvStart` migration remain open.

This module imports only `UniformBarrier` (hence `AnalyticBarrier`,
`InverseGraph`, `AS202Lift` transitively) and adds NO `native_decide` of its own
beyond the tiny finite goal-witness; it is far from the `Cert_m1_Q10` blow-up.
-/

import CollatzLean4.UniformBarrier

namespace CollatzLean4.Admissible

/-! ### Part 1 — The precision-reduction map `projπ` -/

/-- **Precision-reduction map.** Reduce a level-`(m+1)` vertex to its level-`m`
cylinder representative, keeping the depth coordinate `j` fixed:
`projπ m ⟨j, c⟩ = ⟨j, c % 3^(22m+2+j)⟩`. The modulus is the *level-`m`* cylinder
modulus at the vertex's own depth, so `projπ` forgets exactly the 3-adic digits
between precision `22m+2+j` and `22(m+1)+2+j`. -/
def projπ (m : Nat) (v : InvVertex) : InvVertex :=
  ⟨v.j, v.c % 3 ^ (22 * m + 2 + v.j)⟩

@[simp] theorem projπ_j (m : Nat) (v : InvVertex) : (projπ m v).j = v.j := rfl

@[simp] theorem projπ_c (m : Nat) (v : InvVertex) :
    (projπ m v).c = v.c % 3 ^ (22 * m + 2 + v.j) := rfl

/-! ### Part 2 — Modular descent helpers

The single arithmetic fact behind the whole functor: a modular equation at the
larger modulus `3^(22(m+1)+2+j)` descends to the smaller modulus
`3^(22m+2+j)`, because the smaller power divides the larger
(`22m+2+j ≤ 22(m+1)+2+j`). We also re-reduce the `2^τ · c` products so that the
right-hand side mentions the *projected* `c`. -/

/-- The level-`m` modulus divides the level-`(m+1)` modulus at the same depth. -/
theorem pow_lvl_dvd (m j : Nat) :
    (3 : Nat) ^ (22 * m + 2 + j) ∣ 3 ^ (22 * (m + 1) + 2 + j) :=
  pow_dvd_pow 3 (by omega)

/-- Descend a level-`(m+1)` modular equation `a ≡ b (mod 3^(22(m+1)+2+j))` to
level `m`. The smaller power divides the larger, so reducing both sides preserves
the congruence. -/
theorem descend_eq (m j a b : Nat)
    (h : a % 3 ^ (22 * (m + 1) + 2 + j) = b % 3 ^ (22 * (m + 1) + 2 + j)) :
    a % 3 ^ (22 * m + 2 + j) = b % 3 ^ (22 * m + 2 + j) := by
  have hd := pow_lvl_dvd m j
  have := congrArg (· % 3 ^ (22 * m + 2 + j)) h
  simpa only [Nat.mod_mod_of_dvd _ hd] using this

/-- **One-edge consistency descent.** The `InvEdgeOne` consistency clause at level
`(m+1)` descends to its `projπ`-projected level-`m` form. -/
theorem descend_one_cons (m j a τ c : Nat)
    (h : a % 3 ^ (22 * (m + 1) + 2 + j) = (2 ^ τ * c) % 3 ^ (22 * (m + 1) + 2 + j)) :
    (a % 3 ^ (22 * m + 2 + j)) % 3 ^ (22 * m + 2 + j)
      = (2 ^ τ * (c % 3 ^ (22 * m + 2 + j))) % 3 ^ (22 * m + 2 + j) := by
  rw [Nat.mod_mod, descend_eq m j a (2 ^ τ * c) h]
  -- Pull the inner `% 3^(22m+2+j)` through the multiplication.
  exact ((Nat.mod_modEq c _).symm.mul_left _)

/-- **Zero-edge consistency descent.** The `InvEdgeZero` consistency clause at
level `(m+1)`, `(3·v.c + 1) ≡ 2^τ·c (mod 3^(22(m+1)+2+(j+1)))`, descends to its
`projπ`-projected level-`m` form, where the source `c` is now reduced mod the
*smaller* level-`m` modulus `3^(22m+2+j)` and the `3·_+1` is taken mod
`3^(22m+2+(j+1))`. Handles the extra `3·(c % …)` realignment via
`three_mul_mod_pow_succ`. -/
theorem descend_zero_cons (m j a τ c : Nat)
    (h : (3 * a + 1) % 3 ^ (22 * (m + 1) + 2 + (j + 1))
       = (2 ^ τ * c) % 3 ^ (22 * (m + 1) + 2 + (j + 1))) :
    (3 * (a % 3 ^ (22 * m + 2 + j)) + 1) % 3 ^ (22 * m + 2 + (j + 1))
      = (2 ^ τ * (c % 3 ^ (22 * m + 2 + (j + 1)))) % 3 ^ (22 * m + 2 + (j + 1)) := by
  -- Realign the LHS: replace `3 * (a % 3^(22m+2+j))` by `3 * a` at the +1 modulus.
  have hpow : 22 * m + 2 + (j + 1) = (22 * m + 2 + j) + 1 := by omega
  have h_realign :
      (3 * (a % 3 ^ (22 * m + 2 + j)) + 1) % 3 ^ (22 * m + 2 + (j + 1))
        = (3 * a + 1) % 3 ^ (22 * m + 2 + (j + 1)) := by
    rw [hpow, Nat.add_mod, ← three_mul_mod_pow_succ, ← Nat.add_mod]
  rw [h_realign]
  -- Now descend the (m+1)-level equation to level m, then pull the inner mod
  -- through the multiplication on the right.
  rw [descend_eq m (j + 1) (3 * a + 1) (2 ^ τ * c) h]
  exact ((Nat.mod_modEq c _).symm.mul_left _)

/-! ### Part 3 — The core brick: edge projection -/

/-- **Edge projection (the core R2 brick).** `projπ m` sends a level-`(m+1)`
κ-precise edge to a level-`m` κ-precise edge carrying the **same** κ value.

The κ-class is preserved verbatim: `j`-relations are untouched (`projπ` fixes
`j`); `InX (projπ v').c` follows from `InX v'.c` by `InX_mod_pow`; `tau (projπ
v').c = tau v'.c` by `tau_mod_pow` (so the τ-side conditions and κ value
transfer); and the residue-consistency equation descends by `descend_mul_eq`.
The required `2 ≤ 22m+2+j` is automatic. -/
theorem InvKappaPreciseEdge_projectDown
    {m : Nat} {v v' : InvVertex} {κ : Int}
    (h : InvKappaPreciseEdge (22 * (m + 1) + 2) v v' κ) :
    InvKappaPreciseEdge (22 * m + 2) (projπ m v) (projπ m v') κ := by
  -- Helper: `tau` of the projected target equals `tau v'.c` (any depth `k`).
  have h_le2 : ∀ k : Nat, 2 ≤ 22 * m + 2 + k := fun k => by omega
  have h_tau_proj : tau (projπ m v').c = tau v'.c := by
    simp only [projπ_c]; exact tau_mod_pow v'.c _ (h_le2 v'.j)
  rcases h with ⟨ω, h_e, h_k⟩ | ⟨ω, h_e, h_tau, h_k⟩ | ⟨ω, h_e, h_tau, h_k⟩
  · -- One-edge (κ = 1).
    obtain ⟨h_j, h_X, h_cons, _hω⟩ := h_e
    refine Or.inl ⟨(tau (projπ m v').c : Int), ⟨?_, ?_, ?_, rfl⟩, h_k⟩
    · -- j unchanged
      show (projπ m v').j = (projπ m v).j
      simp only [projπ_j]; exact h_j
    · -- InX of projected target
      show InX ((projπ m v').c)
      simp only [projπ_c]
      exact InX_mod_pow v'.c _ h_X (h_le2 v'.j)
    · -- consistency clause, descended
      simp only [projπ_j, projπ_c, h_j]
      rw [tau_mod_pow v'.c (22 * m + 2 + v.j) (h_le2 v.j)]
      -- `h_cons` is already `v.c % 3^(R+v.j) = (2^τ v'.c * v'.c) % 3^(R+v.j)`.
      exact descend_one_cons m v.j v.c (tau v'.c) v'.c h_cons
  · -- τ=1 zero-edge (κ = -1).
    obtain ⟨h_j, h_X, h_cons, _hω⟩ := h_e
    refine Or.inr (Or.inl ⟨(tau (projπ m v').c : Int) - 2, ⟨?_, ?_, ?_, rfl⟩, ?_, h_k⟩)
    · -- j ↦ j+1
      show (projπ m v').j = (projπ m v).j + 1
      simp only [projπ_j]; exact h_j
    · show InX ((projπ m v').c)
      simp only [projπ_c]
      exact InX_mod_pow v'.c _ h_X (h_le2 v'.j)
    · -- consistency clause for the zero-edge, descended
      simp only [projπ_j, projπ_c, h_j]
      rw [tau_mod_pow v'.c (22 * m + 2 + (v.j + 1)) (h_le2 (v.j + 1))]
      have h_cons' : (3 * v.c + 1) % 3 ^ (22 * (m + 1) + 2 + (v.j + 1))
                   = (2 ^ tau v'.c * v'.c) % 3 ^ (22 * (m + 1) + 2 + (v.j + 1)) := by
        have := h_cons; rw [h_j] at this; exact this
      exact descend_zero_cons m v.j v.c (tau v'.c) v'.c h_cons'
    · -- τ-side condition: tau (projπ v').c = 1
      rw [h_tau_proj]; exact h_tau
  · -- τ≥2 zero-edge (κ = 0).
    obtain ⟨h_j, h_X, h_cons, _hω⟩ := h_e
    refine Or.inr (Or.inr ⟨(tau (projπ m v').c : Int) - 2, ⟨?_, ?_, ?_, rfl⟩, ?_, h_k⟩)
    · show (projπ m v').j = (projπ m v).j + 1
      simp only [projπ_j]; exact h_j
    · show InX ((projπ m v').c)
      simp only [projπ_c]
      exact InX_mod_pow v'.c _ h_X (h_le2 v'.j)
    · -- consistency clause for the zero-edge, descended
      simp only [projπ_j, projπ_c, h_j]
      rw [tau_mod_pow v'.c (22 * m + 2 + (v.j + 1)) (h_le2 (v.j + 1))]
      have h_cons' : (3 * v.c + 1) % 3 ^ (22 * (m + 1) + 2 + (v.j + 1))
                   = (2 ^ tau v'.c * v'.c) % 3 ^ (22 * (m + 1) + 2 + (v.j + 1)) := by
        have := h_cons; rw [h_j] at this; exact this
      exact descend_zero_cons m v.j v.c (tau v'.c) v'.c h_cons'
    · -- τ-side condition: 2 ≤ tau (projπ v').c
      rw [h_tau_proj]; exact h_tau

/-! ### Part 4 — Path-level functoriality -/

/-- **Path projection (functoriality).** A level-`(m+1)` κ-precise path maps under
`projπ m` to a level-`m` κ-precise path with the **same** total κ-cost and the
pointwise-projected interior vertex list. Pure induction on the path, applying
`InvKappaPreciseEdge_projectDown` at every edge. -/
theorem WPath_projectDown
    {m : Nat} {s t : InvVertex} {κ : Int} {vs : List InvVertex}
    (h : WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) s t κ vs) :
    WPath (InvKappaPreciseEdge (22 * m + 2)) (projπ m s) (projπ m t) κ
      (vs.map (projπ m)) := by
  induction vs generalizing s κ with
  | nil =>
      simp only [WPath] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | cons v vs' ih =>
      simp only [WPath] at h
      obtain ⟨κ₁, κ₂, h_edge, h_rest, rfl⟩ := h
      refine ⟨κ₁, κ₂, InvKappaPreciseEdge_projectDown h_edge, ih h_rest, rfl⟩

/-! ### Part 5 — Goal descent (and its honest failure of reflection) -/

/-- **Goals descend.** A level-`(m+1)` goal projects to a level-`m` goal: if
`v.c ≡ 1 (mod 3^(22(m+1)+2+j))` then `(projπ m v).c ≡ 1 (mod 3^(22m+2+j))`. The
smaller power divides the larger, so reducing both sides preserves the
congruence. -/
theorem IsGoal_projectDown
    {m : Nat} {v : InvVertex}
    (h : InvVertex.IsGoal v (22 * (m + 1) + 2)) :
    InvVertex.IsGoal (projπ m v) (22 * m + 2) := by
  -- IsGoal v R : v.c % 3^(R+v.j) = 1 % 3^(R+v.j)
  show (projπ m v).c % 3 ^ (22 * m + 2 + (projπ m v).j)
     = 1 % 3 ^ (22 * m + 2 + (projπ m v).j)
  simp only [projπ_j, projπ_c]
  rw [Nat.mod_mod]
  have hd := pow_lvl_dvd m v.j
  have hh : v.c % 3 ^ (22 * (m + 1) + 2 + v.j) = 1 % 3 ^ (22 * (m + 1) + 2 + v.j) := h
  have := congrArg (· % 3 ^ (22 * m + 2 + v.j)) hh
  simpa only [Nat.mod_mod_of_dvd _ hd] using this

/-- **Reverse-lift obstruction (the honest companion).** The converse of
`IsGoal_projectDown` is FALSE: there is a vertex whose `projπ`-image is a
level-`m` goal while the vertex itself is *not* a level-`(m+1)` goal.

Witness (at `m = 1`): `v = ⟨0, 1 + 3^24⟩`. Then
`projπ 1 v = ⟨0, (1+3^24) % 3^24⟩ = ⟨0, 1⟩`, a level-1 goal (`1 ≡ 1 mod 3^24`);
but `v.c = 1 + 3^24 ≢ 1 (mod 3^46)`, so `v` is not a level-2 goal.

Consequence for the reduction: `projπ` is many-to-one, so a *projected* prefix
arriving at a level-`m` goal does **not** pin down the level-`(m+1)` split point.
R2 therefore reduces `KappaPathSplit` to — but cannot by itself discharge — the
existence of a genuine `(m+1)`-level cut, matching `kappa_no_canonical_depth_cut`.
-/
theorem IsGoal_projectDown_not_reflects :
    ∃ (m : Nat) (v : InvVertex),
      InvVertex.IsGoal (projπ m v) (22 * m + 2) ∧
      ¬ InvVertex.IsGoal v (22 * (m + 1) + 2) := by
  refine ⟨1, ⟨0, 1 + 3 ^ 24⟩, ?_, ?_⟩
  · -- projπ 1 ⟨0, 1+3^24⟩ = ⟨0, 1⟩ is a level-1 goal: (1 + 3^24) ≡ 1 (mod 3^24).
    show ((1 + 3 ^ 24) % 3 ^ (22 * 1 + 2 + 0)) % 3 ^ (22 * 1 + 2 + 0)
       = 1 % 3 ^ (22 * 1 + 2 + 0)
    have hmod : 22 * 1 + 2 + 0 = 24 := by norm_num
    rw [hmod]
    -- (1 + 3^24) % 3^24 = 1, then double mod and `1 % 3^24 = 1`.
    have h_one_lt_24 : (1 : Nat) < 3 ^ 24 := by
      have h : (3 : Nat) ^ 1 ≤ 3 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      simp only [pow_one] at h; omega
    have h1 : (1 + 3 ^ 24) % 3 ^ 24 = 1 := by
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt h_one_lt_24]
    rw [h1]
  · -- ⟨0, 1+3^24⟩ is NOT a level-2 goal (mod 3^46): 1 + 3^24 ≠ 1 and both < 3^46.
    show ¬ ((1 + 3 ^ 24) % 3 ^ (22 * (1 + 1) + 2 + 0) = 1 % 3 ^ (22 * (1 + 1) + 2 + 0))
    have hmod : 22 * (1 + 1) + 2 + 0 = 46 := by norm_num
    rw [hmod]
    have h_lt : (1 : Nat) + 3 ^ 24 < 3 ^ 46 := by
      have : (3 : Nat) ^ 24 < 3 ^ 46 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      omega
    have h_one_lt_46 : (1 : Nat) < 3 ^ 46 := by
      have h : (3 : Nat) ^ 1 ≤ 3 ^ 46 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      simp only [pow_one] at h; omega
    rw [Nat.mod_eq_of_lt h_lt, Nat.mod_eq_of_lt h_one_lt_46]
    -- 1 + 3^24 ≠ 1 since 3^24 > 0.
    have : (0 : Nat) < 3 ^ 24 := by positivity
    omega

/-! ### Part 6 — Start vertex fixed point (with caveat C) -/

/-- **`projπ` fixes the start vertex.** `projπ m (InvStart (m+1)) = InvStart m`.

CAVEAT C (flagged, not assumed away): this holds *only* because `InvStart k :=
⟨0, aS202 % 3^(22k+2)⟩` reuses the single low-precision constant
`aS202 = 1 + 3^22 < 3^24`, which is `< 3^(22k+2)` for every `k ≥ 1`, so
`InvStart k = ⟨0, aS202⟩` independently of `k`. By
`aS202_at_2_ne_aS202_mod_3_46`, `aS202` is the *wrong* S202 fixed-point
representative for `m ≥ 2`; so although `projπ` fixes this start, the start
itself is the wrong cylinder above `m = 1`. The honest fix is to migrate
`InvStart` to `aS202_at m` before using the IH barrier on the projected prefix
for `m ≥ 2`. -/
theorem projπ_InvStart (m : Nat) (hm : 1 ≤ m) :
    projπ m (InvStart (m + 1)) = InvStart m := by
  -- `aS202 < 3^(22m+2)` (since `aS202 = 1 + 3^22 < 3^24 ≤ 3^(22m+2)`).
  have h_aS_lt : aS202 < 3 ^ (22 * m + 2) := by
    rw [aS202_decomp]
    have h2 : (3 : Nat) ^ 24 ≤ 3 ^ (22 * m + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (1 : Nat) + 3 ^ 22 < 3 ^ 24 := by norm_num
    omega
  -- The whole equality reduces to the `c`-field (both `j`-fields are `0` by `rfl`).
  -- `c`-field of LHS: `(aS202 % 3^(22(m+1)+2)) % 3^(22m+2+0)`; of RHS: `aS202 % 3^(22m+2)`.
  have hc : ((InvStart (m + 1)).c) % 3 ^ (22 * m + 2 + (InvStart (m + 1)).j)
              = (InvStart m).c := by
    -- `(InvStart (m+1)).j = 0` and `(InvStart (m+1)).c = aS202` (reduced).
    have e1 : (InvStart (m + 1)).c = aS202 := invStart_c_eq_aS202 (m + 1) (by omega)
    have e2 : (InvStart m).c = aS202 := invStart_c_eq_aS202 m hm
    have ej : (InvStart (m + 1)).j = 0 := rfl
    rw [ej, Nat.add_zero, e1, e2]
    exact Nat.mod_eq_of_lt h_aS_lt
  -- Assemble componentwise: LHS is `projπ`'s unfold; rewrite the `c`-field via `hc`.
  show (⟨(InvStart (m + 1)).j,
         (InvStart (m + 1)).c % 3 ^ (22 * m + 2 + (InvStart (m + 1)).j)⟩ : InvVertex)
       = InvStart m
  rw [hc]
  -- Now `(⟨(InvStart (m+1)).j, (InvStart m).c⟩ : InvVertex) = InvStart m`; both `j = 0`.
  show (⟨0, (InvStart m).c⟩ : InvVertex) = InvStart m
  rfl

/-! ### Part 7 — The discharged R2 hypothesis as a named `Prop`

We isolate exactly the R2 precision-tower step — "every qualifying level-`(m+1)`
κ-path becomes a level-`m` κ-path from `InvStart m` to a projected goal, with the
same κ" — as a named `Prop`, and *prove it* from the functor above (for `m ≥ 1`,
where the start fixed-point holds). This removes the precision-tower obligation
from the open set: in the residual reduction of `KappaPathSplit`, R2's
"projected prefix is a genuine `m`-level κ-path to an `m`-goal" is no longer a
hypothesis but a theorem. -/

/-- **R2 precision-tower step (named).** For the `(m+1)`-cylinder: every κ-path
from `InvStart (m+1)` to a level-`(m+1)` goal projects to a κ-path from
`InvStart m` to a level-`m` goal of the **same** total κ-cost. -/
def KappaProjectsDown (m : Nat) : Prop :=
  ∀ {goal : InvVertex} {κ : Int} {vs : List InvVertex},
    InvVertex.IsGoal goal (22 * (m + 1) + 2) →
    WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) goal κ vs →
    ∃ (goal' : InvVertex) (vs' : List InvVertex),
      InvVertex.IsGoal goal' (22 * m + 2) ∧
      WPath (InvKappaPreciseEdge (22 * m + 2)) (InvStart m) goal' κ vs'

/-- **R2 precision-tower step is DISCHARGED** (for `m ≥ 1`). Direct from
`WPath_projectDown` (functoriality), `IsGoal_projectDown` (goal descent) and
`projπ_InvStart` (start fixed point). The projected goal is `projπ m goal`, the
projected vertex list is `vs.map (projπ m)`, and the κ-cost is unchanged.

This is the concrete payoff: R2's precision-reduction obligation is now a Lean
theorem, not an open hypothesis. (Caveat C still applies for `m ≥ 2`: the start
`InvStart m` is the wrong cylinder there; this lemma is nonetheless true as
stated, because it is a statement *about the graph objects `InvStart`*, not a
claim that `InvStart m` is the correct S202 representative.) -/
theorem kappaProjectsDown_holds (m : Nat) (hm : 1 ≤ m) : KappaProjectsDown m := by
  intro goal κ vs h_g h_path
  refine ⟨projπ m goal, vs.map (projπ m), IsGoal_projectDown h_g, ?_⟩
  have h_proj := WPath_projectDown h_path
  rwa [projπ_InvStart m hm] at h_proj

/-! ### Part 8 — κ is preserved (audit lemma)

A one-line audit that the functor does not perturb the weight: the projected path
carries *exactly* the same κ as the original. This is the property R2 relies on —
the m-barrier `(m : Int) ≤ κ` applied to the projected path is a bound on the
*original* κ. -/

/-- **κ-preservation audit.** The total κ-cost is invariant under `projπ`: the
projected path produced by `kappaProjectsDown_holds` has the identical κ. (This
is immediate from the statement of `KappaProjectsDown`, recorded explicitly so
downstream uses can cite κ-invariance directly.) -/
theorem kappaProjectsDown_preserves_kappa
    {m : Nat} (hm : 1 ≤ m)
    {goal : InvVertex} {κ : Int} {vs : List InvVertex}
    (h_g : InvVertex.IsGoal goal (22 * (m + 1) + 2))
    (h_path : WPath (InvKappaPreciseEdge (22 * (m + 1) + 2)) (InvStart (m + 1)) goal κ vs) :
    ∃ (goal' : InvVertex) (vs' : List InvVertex),
      InvVertex.IsGoal goal' (22 * m + 2) ∧
      WPath (InvKappaPreciseEdge (22 * m + 2)) (InvStart m) goal' κ vs' :=
  kappaProjectsDown_holds m hm h_g h_path

end CollatzLean4.Admissible
