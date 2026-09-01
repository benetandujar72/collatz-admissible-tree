/-
S243 — GATE H authenticated: the feature-linear potential classes END here.

`BitlenPotential.lean` proves the bounded κ-barrier with the closed-form potential
`PhiBitlen = ⌊(size−1)/4⌋ + j − Q`, up to the bit criterion `4(m+Q)+1 ≤ size(start)`
— for m = 1 (35-bit start `aS202`), up to `Q = 7` (`kappa_barrier_m1_Q7`).  This
module proves the matching IMPOSSIBILITY results, machine-checking the OTHER side
of the wall.  Both proofs are Farkas certificates produced by the S243 GATE-H
linear program with constraint generation (`tools/phi_hybrid_gate.py`) and
re-verified here from first principles: each row is a TRUE edge/goal/start
constraint of the inverse cylinder graph, and a nonnegative rational combination
of the rows is contradictory — so NO parameter choice satisfies the contract.

  * `no_linear_size_potential_m1_Q8` — **the (1, j, size)-linear class is dead at
    Q = 8** (m = 1): no rational `θ₀ + θ₁·j + θ₂·size(c mod 3^{24+j})` satisfies
    the bounded-slice potential contract of
    `S202_kappa_precise_barrier_bounded_from_potential` at (m, Q) = (1, 8).
    With `kappa_barrier_m1_Q7`, the wall for this class sits EXACTLY at the bit
    criterion (`Q ≤ 7.5`): Q = 7 provable, Q = 8 impossible.  Four rows:
    start + goal + one τ=1 zero-edge + one τ=4 one-edge, multipliers
    (2, 2, 16, 17)/37.

  * `linear_size_potential_m1_Q7` — the linear relaxation of `PhiBitlen`,
    `θ = (−29/4, 1, 1/4, 0, 0)`, satisfies the universal contract at (1, 7): the wall of
    the linear class is machine-checked on BOTH sides.

  * `no_hybrid_potential_m1_Q8` — **the singular attractor poles do not move the wall**:
    adding the two Green-style features `ν₃(c−1)` and `ν₃(c+1)` (the poles at the τ=2
    attractor `c ≡ 1`, identity `4(y−1) = 3(c−1)`, and the τ=1 filament attractor
    `c ≡ −1`, identity `2(y+1) = 3(c+1)`) leaves the class dead at the SAME step
    (1, 8).  Six rows, multipliers (1798, 1798, 14877, 13888, 496, 564)/33421.  The
    decisive row is the goal's own one-edge predecessor `(8,4) → (8,1)`: the mod-9 trap
    (source class 4) sits next to the goal and `ν₃(c−1)` jumps `1 → 32` at κ = +1.
    (`no_hybrid_potential_m1_Q9`, the earlier six-row certificate at (1, 9), is kept; it
    is implied by monotonicity in Q.)

Numerical context (GATE H sweep with universal in-slice rows, exact rational Farkas at
every dead point): both classes are alive Q ≤ 7 / dead Q ≥ 8 at m = 1 and alive Q ≤ 16 /
dead Q ≥ 17 at m = 2 (73-bit faithful start) — exactly the bit criterion.  A first
version of the separation oracle harvested only start-reachable edges and reported the
enriched class alive one step longer; the explicit in-slice families (notably the
goal-adjacent trap edge) corrected this — a survivor verdict is never a feasibility proof.

SCOPE (honest): these theorems kill the LINEAR-feature classes against the
bounded-slice potential contract (the shape every Lean potential lemma in this
corpus uses).  They do NOT exclude non-linear integer potentials — the exact
value function always works when the barrier is true (e.g. the Q = 8 certificate
`Cert_m1_Q8_S216_Barrier`); the content is that no CLOSED-FORM member of these
feature classes reaches it.

Axioms target: {propext, Classical.choice, Quot.sound}.  Builds narrow.
-/

import CollatzLean4.AnalyticBarrier
import CollatzLean4.BitlenPotential

namespace CollatzLean4.Admissible

/-! ### The feature potential -/

/-- Fuel-based 3-adic valuation of a residue: `nu3fuel depth x` is `ν₃(x)` for
`0 < x < 3^depth`, and `depth` itself for `x = 0` (the "full depth" convention
for the zero residue — the pole value). -/
def nu3fuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, x => if x % 3 = 0 then nu3fuel fuel (x / 3) + 1 else 0

/-- The hybrid feature potential on inverse-graph vertices (m = 1 moduli,
`R = 24`): constant + `j` + bit-size of the canonical residue + the two singular
attractor poles `ν₃((c−1) mod 3^{24+j})` and `ν₃((c+1) mod 3^{24+j})` (with the
zero residue valued at full depth).  Setting `θ₃ = θ₄ = 0` recovers the
(1, j, size)-linear class of `PhiBitlen`. -/
def PhiHyb (θ0 θ1 θ2 θ3 θ4 : ℚ) (v : InvVertex) : ℚ :=
  θ0 + θ1 * v.j + θ2 * Nat.size (v.c % 3 ^ (24 + v.j))
    + θ3 * nu3fuel (24 + v.j)
        ((v.c % 3 ^ (24 + v.j) + (3 ^ (24 + v.j) - 1)) % 3 ^ (24 + v.j))
    + θ4 * nu3fuel (24 + v.j) ((v.c % 3 ^ (24 + v.j) + 1) % 3 ^ (24 + v.j))

/-- Evaluation of `PhiHyb` at a concrete vertex from kernel-checked feature
values (bit-size `s`, pole depths `p`, `q`). -/
theorem PhiHyb_eval (θ0 θ1 θ2 θ3 θ4 : ℚ) (j c s p q : Nat)
    (hs : Nat.size (c % 3 ^ (24 + j)) = s)
    (hp : nu3fuel (24 + j) ((c % 3 ^ (24 + j) + (3 ^ (24 + j) - 1)) % 3 ^ (24 + j)) = p)
    (hq : nu3fuel (24 + j) ((c % 3 ^ (24 + j) + 1) % 3 ^ (24 + j)) = q) :
    PhiHyb θ0 θ1 θ2 θ3 θ4 ⟨j, c⟩
      = θ0 + θ1 * j + θ2 * s + θ3 * p + θ4 * q := by
  show θ0 + θ1 * (j : ℚ) + θ2 * (Nat.size (c % 3 ^ (24 + j)) : ℚ)
      + θ3 * (nu3fuel (24 + j)
          ((c % 3 ^ (24 + j) + (3 ^ (24 + j) - 1)) % 3 ^ (24 + j)) : ℚ)
      + θ4 * (nu3fuel (24 + j) ((c % 3 ^ (24 + j) + 1) % 3 ^ (24 + j)) : ℚ)
      = θ0 + θ1 * j + θ2 * s + θ3 * p + θ4 * q
  rw [hs, hp, hq]

/-! ### The certificate rows: true edges of the inverse graph

All four κ-precise edges below are EXACT integer identities (no modular wrap):
`2^τ · c' = 3c + 1` (zero-edges) or `2^τ · c' = c` (one-edges), kernel-checked. -/

/-- TH1/E1: the τ=1 zero-edge (κ = −1) `(2, 1129718145925) → (3, 1694577218888)`;
`2 · 1694577218888 = 3 · 1129718145925 + 1`. -/
theorem hybA_edge1 :
    InvKappaPreciseEdge 24 ⟨2, 1129718145925⟩ ⟨3, 1694577218888⟩ (-1) :=
  Or.inr (Or.inl ⟨-1, by unfold InvEdgeZero InX; decide, by decide, rfl⟩)

/-- TH1/E2: the τ=4 one-edge (κ = +1) `(6, 182637341717152) → (6, 11414833857322)`;
`16 · 11414833857322 = 182637341717152` — the bit-crash edge forcing `θ₂ ≤ 1/4`. -/
theorem hybA_edge2 :
    InvKappaPreciseEdge 24 ⟨6, 182637341717152⟩ ⟨6, 11414833857322⟩ 1 :=
  Or.inl ⟨4, by unfold InvEdgeOne InX; decide, rfl⟩

/-- TH2/E1: the τ=1 zero-edge (κ = −1) `(3, 4871909504303) → (4, 7307864256455)`. -/
theorem hybB_edge1 :
    InvKappaPreciseEdge 24 ⟨3, 4871909504303⟩ ⟨4, 7307864256455⟩ (-1) :=
  Or.inr (Or.inl ⟨-1, by unfold InvEdgeZero InX; decide, by decide, rfl⟩)

/-- TH2/E2: the τ=4 one-edge (κ = +1) `(9, 4975302956326384) → (9, 310956434770399)`. -/
theorem hybB_edge2 :
    InvKappaPreciseEdge 24 ⟨9, 4975302956326384⟩ ⟨9, 310956434770399⟩ 1 :=
  Or.inl ⟨4, by unfold InvEdgeOne InX; decide, rfl⟩

/-- TH2/E3: the τ=2 DEEP-JUMP one-edge (κ = +1)
`(9, 2462147789600812) → (9, 615536947400203)`: the target has `ν₃(c−1) = 8`
against the source's `1` — the mod-9 trap edge that pins the pole coefficient. -/
theorem hybB_edge3 :
    InvKappaPreciseEdge 24 ⟨9, 2462147789600812⟩ ⟨9, 615536947400203⟩ 1 :=
  Or.inl ⟨2, by unfold InvEdgeOne InX; decide, rfl⟩

/-- TH2/E4: the τ=2 zero-edge (κ = 0) `(8, 1493722122425261) → (9, 1120291591818946)`:
leaves the `−1` pole shell (`ν₃(c+1)`: 9 → 0), pinning the second pole. -/
theorem hybB_edge4 :
    InvKappaPreciseEdge 24 ⟨8, 1493722122425261⟩ ⟨9, 1120291591818946⟩ 0 :=
  Or.inr (Or.inr ⟨0, by unfold InvEdgeZero InX; decide, by decide, rfl⟩)

/-! ### Theorem 1 — the (1, j, size)-linear class is dead at (m, Q) = (1, 8) -/

/-- **The exact wall of the bit-length class.**  No rational linear potential
`θ₀ + θ₁·j + θ₂·size(c mod 3^{24+j})` satisfies the bounded-slice κ-potential
contract at (m, Q) = (1, 8).  Together with `kappa_barrier_m1_Q7` (the class
member `PhiBitlen` certifies Q = 7), the wall for this class sits exactly at the
bit criterion `4(1+Q)+1 ≤ 35`.  Farkas multipliers: (2, 2, 16, 17)/37. -/
theorem no_linear_size_potential_m1_Q8 :
    ¬ ∃ θ0 θ1 θ2 : ℚ,
      (∀ (v v' : InvVertex) (κ : Int), v.j ≤ 8 → v'.j ≤ 8 →
          InvKappaPreciseEdge 24 v v' κ →
          PhiHyb θ0 θ1 θ2 0 0 v ≤ (κ : ℚ) + PhiHyb θ0 θ1 θ2 0 0 v') ∧
      (∀ v : InvVertex, InvVertex.IsGoal v 24 → v.j ≤ 8 →
          PhiHyb θ0 θ1 θ2 0 0 v ≤ 0) ∧
      ((1 : ℚ) ≤ PhiHyb θ0 θ1 θ2 0 0 (InvStart 1)) := by
  rintro ⟨θ0, θ1, θ2, h_edge, h_goal, h_start⟩
  rw [show InvStart 1 = (⟨0, 31381059610⟩ : InvVertex) from by decide,
      PhiHyb_eval θ0 θ1 θ2 0 0 0 31381059610 35 22 0
        (by decide) (by decide) (by decide)] at h_start
  have hG := h_goal ⟨8, 1⟩ rfl (by decide)
  rw [PhiHyb_eval θ0 θ1 θ2 0 0 8 1 1 32 0
        (by decide) (by decide) (by decide)] at hG
  have hE1 := h_edge _ _ _ (by decide) (by decide) hybA_edge1
  rw [PhiHyb_eval θ0 θ1 θ2 0 0 2 1129718145925 41 24 0
        (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 0 0 3 1694577218888 41 0 1
        (by decide) (by decide) (by decide)] at hE1
  have hE2 := h_edge _ _ _ (by decide) (by decide) hybA_edge2
  rw [PhiHyb_eval θ0 θ1 θ2 0 0 6 182637341717152 48 1 0
        (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 0 0 6 11414833857322 44 1 0
        (by decide) (by decide) (by decide)] at hE2
  push_cast at h_start hG hE1 hE2
  linarith

/-! ### Theorem 1′ — the linear class is ALIVE at (m, Q) = (1, 7): the wall is exact

The linear relaxation of `PhiBitlen`, `θ = (−29/4, 1, 1/4, 0, 0)`, satisfies the universal
contract at `(1, 7)` directly from the size laws (`oneEdge_size_le`, `zeroEdge_size_le`,
`tau_le_four`).  Together with `no_linear_size_potential_m1_Q8` this pins the wall of the
linear class machine-checked on BOTH sides: alive at `Q = 7`, dead at `Q = 8`. -/

theorem phiLin_edge :
    ∀ (v v' : InvVertex) (κ : Int), v.j ≤ 7 → v'.j ≤ 7 →
      InvKappaPreciseEdge 24 v v' κ →
      PhiHyb (-29/4) 1 (1/4) 0 0 v ≤ (κ : ℚ) + PhiHyb (-29/4) 1 (1/4) 0 0 v' := by
  intro v v' κ _ _ hedge
  unfold PhiHyb
  rcases hedge with ⟨ω, he, hκ⟩ | ⟨ω, he, hτ, hκ⟩ | ⟨ω, he, hτ, hκ⟩
  · -- one-edge: same level, size drops by at most 4, κ = +1
    have hj : v'.j = v.j := he.1
    have hs := oneEdge_size_le (R := 24) (by norm_num) he
    subst hκ
    rw [hj]
    have hs' : (Nat.size (v.c % 3 ^ (24 + v.j)) : ℚ)
        ≤ (Nat.size (v'.c % 3 ^ (24 + v.j)) : ℚ) + 4 := by exact_mod_cast hs
    push_cast
    linarith
  · -- zero-edge, τ = 1: κ = −1, size does not grow
    have hj : v'.j = v.j + 1 := he.1
    have hs := zeroEdge_size_le (R := 24) (by norm_num) he
    rw [hτ] at hs
    subst hκ
    have hs' : (Nat.size (v.c % 3 ^ (24 + v.j)) : ℚ) + 1
        ≤ (Nat.size (v'.c % 3 ^ (24 + v'.j)) : ℚ) + 1 := by exact_mod_cast hs
    have hjq : (v'.j : ℚ) = (v.j : ℚ) + 1 := by rw [hj]; push_cast; ring
    push_cast
    linarith
  · -- zero-edge, τ ≥ 2: κ = 0, size grows by at most τ − 1 ≤ 3
    have hj : v'.j = v.j + 1 := he.1
    have hs := zeroEdge_size_le (R := 24) (by norm_num) he
    have ht4 := tau_le_four v'.c
    subst hκ
    have hs' : (Nat.size (v.c % 3 ^ (24 + v.j)) : ℚ) + 1
        ≤ (Nat.size (v'.c % 3 ^ (24 + v'.j)) : ℚ) + 4 := by
      have : Nat.size (v.c % 3 ^ (24 + v.j)) + 1
          ≤ Nat.size (v'.c % 3 ^ (24 + v'.j)) + 4 := by omega
      exact_mod_cast this
    have hjq : (v'.j : ℚ) = (v.j : ℚ) + 1 := by rw [hj]; push_cast; ring
    push_cast
    linarith

theorem phiLin_goal :
    ∀ v : InvVertex, InvVertex.IsGoal v 24 → v.j ≤ 7 →
      PhiHyb (-29/4) 1 (1/4) 0 0 v ≤ 0 := by
  intro v hg hj
  have hc : v.c % 3 ^ (24 + v.j) = 1 := by
    have hg' : v.c % 3 ^ (24 + v.j) = 1 % 3 ^ (24 + v.j) := hg
    have h1 : (1 : ℕ) % 3 ^ (24 + v.j) = 1 :=
      Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
    exact hg'.trans h1
  have hs1 : Nat.size 1 = 1 := by decide
  unfold PhiHyb
  rw [hc, hs1]
  have hjq : (v.j : ℚ) ≤ 7 := by exact_mod_cast hj
  push_cast
  linarith

theorem phiLin_start : (1 : ℚ) ≤ PhiHyb (-29/4) 1 (1/4) 0 0 (InvStart 1) := by
  rw [show InvStart 1 = (⟨0, 31381059610⟩ : InvVertex) from by decide,
      PhiHyb_eval (-29/4) 1 (1/4) 0 0 0 31381059610 35 22 0
        (by decide) (by decide) (by decide)]
  norm_num

/-- **The linear class is alive at `(1, 7)`**: the linear relaxation of `PhiBitlen` satisfies
the universal contract.  With `no_linear_size_potential_m1_Q8`, the wall is exact. -/
theorem linear_size_potential_m1_Q7 :
    ∃ θ0 θ1 θ2 : ℚ,
      (∀ (v v' : InvVertex) (κ : Int), v.j ≤ 7 → v'.j ≤ 7 →
          InvKappaPreciseEdge 24 v v' κ →
          PhiHyb θ0 θ1 θ2 0 0 v ≤ (κ : ℚ) + PhiHyb θ0 θ1 θ2 0 0 v') ∧
      (∀ v : InvVertex, InvVertex.IsGoal v 24 → v.j ≤ 7 →
          PhiHyb θ0 θ1 θ2 0 0 v ≤ 0) ∧
      ((1 : ℚ) ≤ PhiHyb θ0 θ1 θ2 0 0 (InvStart 1)) :=
  ⟨-29/4, 1, 1/4, phiLin_edge, phiLin_goal, phiLin_start⟩

/-! ### Theorem 2 — the hybrid class with attractor poles is ALREADY dead at (m, Q) = (1, 8)

The universal contract quantifies over EVERY edge of the slice `j ≤ Q`, reachable or
not.  Four explicit in-slice edges settle the pole-enriched class one step EARLIER than
the reachable-region oracle first suggested: the τ=4 one-edge `(0,112) → (0,7)` (the
`θ₂ ≤ 1/4` enforcer), a τ=1 zero-edge (`θ₁ ≥ 1 + θ₄`), the τ=2 zero-edge off the deep
`−1` shell `(5, 2·3²⁸−1) → (6, (3²⁹−1)/2)` (pins `θ₄`), and — the decisive row — the
goal's own one-edge predecessor `(8,4) → (8,1)`: the mod-9 trap (source class `4`,
`oneEdge_deepjump_source_four`) sits immediately next to the goal, and along that single
κ=+1 edge `ν₃(c−1)` jumps from `1` to the full depth `32`, so any negative pole weight
`θ₃` is capped by `2θ₂ − 31θ₃ ≤ 1`.  Multipliers `(1798, 1798, 14877, 13888, 496, 564)/33421`.
Consequence: the wall of the enriched class coincides EXACTLY with the wall of the
linear class (Theorem 1) — the attractor poles buy nothing under the universal contract. -/

theorem trapA_edge1 : InvKappaPreciseEdge 24 ⟨0, 112⟩ ⟨0, 7⟩ 1 :=
  Or.inl ⟨4, by unfold InvEdgeOne InX; decide, rfl⟩

theorem trapA_edge2 : InvKappaPreciseEdge 24 ⟨0, 17⟩ ⟨1, 26⟩ (-1) :=
  Or.inr (Or.inl ⟨-1, by unfold InvEdgeZero InX; decide, by decide, rfl⟩)

/-- The τ=2 zero-edge leaving the deep `−1` shell: `c = 2·3²⁸ − 1 ≡ −1 (mod 3²⁸)`,
`4c' = 3c + 1` with `c' = (3²⁹ − 1)/2`; `ν₃(c+1)` crashes from `28` to `0`. -/
theorem trapA_edge3 :
    InvKappaPreciseEdge 24 ⟨5, 45753584909921⟩ ⟨6, 34315188682441⟩ 0 :=
  Or.inr (Or.inr ⟨0, by unfold InvEdgeZero InX; decide, by decide, rfl⟩)

/-- The goal's one-edge predecessor at level 8: `4 = 2² · 1`, κ = +1; `ν₃(c−1)`: `1 → 32`. -/
theorem trapA_edge4 : InvKappaPreciseEdge 24 ⟨8, 4⟩ ⟨8, 1⟩ 1 :=
  Or.inl ⟨2, by unfold InvEdgeOne InX; decide, rfl⟩

/-- **The attractor poles buy nothing.**  No rational potential
`θ₀ + θ₁·j + θ₂·size + θ₃·ν₃(c−1) + θ₄·ν₃(c+1)` satisfies the bounded-slice contract at
`(m, Q) = (1, 8)` — the same step at which the linear class dies
(`no_linear_size_potential_m1_Q8`).  Six rows, the decisive one being the goal-adjacent
trap edge `trapA_edge4`. -/
theorem no_hybrid_potential_m1_Q8 :
    ¬ ∃ θ0 θ1 θ2 θ3 θ4 : ℚ,
      (∀ (v v' : InvVertex) (κ : Int), v.j ≤ 8 → v'.j ≤ 8 →
          InvKappaPreciseEdge 24 v v' κ →
          PhiHyb θ0 θ1 θ2 θ3 θ4 v ≤ (κ : ℚ) + PhiHyb θ0 θ1 θ2 θ3 θ4 v') ∧
      (∀ v : InvVertex, InvVertex.IsGoal v 24 → v.j ≤ 8 →
          PhiHyb θ0 θ1 θ2 θ3 θ4 v ≤ 0) ∧
      ((1 : ℚ) ≤ PhiHyb θ0 θ1 θ2 θ3 θ4 (InvStart 1)) := by
  rintro ⟨θ0, θ1, θ2, θ3, θ4, h_edge, h_goal, h_start⟩
  rw [show InvStart 1 = (⟨0, 31381059610⟩ : InvVertex) from by decide,
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 0 31381059610 35 22 0
        (by decide) (by decide) (by decide)] at h_start
  have hG := h_goal ⟨8, 1⟩ rfl (by decide)
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 8 1 1 32 0
        (by decide) (by decide) (by decide)] at hG
  have hE1 := h_edge _ _ _ (by decide) (by decide) trapA_edge1
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 0 112 7 1 0 (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 0 7 3 1 0 (by decide) (by decide) (by decide)] at hE1
  have hE2 := h_edge _ _ _ (by decide) (by decide) trapA_edge2
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 0 17 5 0 2 (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 1 26 5 0 3 (by decide) (by decide) (by decide)] at hE2
  have hE3 := h_edge _ _ _ (by decide) (by decide) trapA_edge3
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 5 45753584909921 46 0 28
        (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 6 34315188682441 45 1 0
        (by decide) (by decide) (by decide)] at hE3
  have hE4 := h_edge _ _ _ (by decide) (by decide) trapA_edge4
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 8 4 3 1 0 (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 8 1 1 32 0 (by decide) (by decide) (by decide)] at hE4
  push_cast at h_start hG hE1 hE2 hE3 hE4
  linarith

/-! ### Theorem 2′ — the earlier six-row certificate at (m, Q) = (1, 9) (kept: true, not sharp) -/


/-- **The attractor poles buy exactly one zero-edge.**  No rational potential
`θ₀ + θ₁·j + θ₂·size + θ₃·ν₃(c−1) + θ₄·ν₃(c+1)` (poles at the two attractors,
zero residue at full depth) satisfies the bounded-slice contract at
(m, Q) = (1, 9) — while the GATE-H LP is feasible for this class at Q = 8.
Farkas multipliers: (280, 280, 2268, 2115, 404, 252)/5599; the deep-jump trap
edge `hybB_edge3` is the row that pins the pole coefficient. -/
theorem no_hybrid_potential_m1_Q9 :
    ¬ ∃ θ0 θ1 θ2 θ3 θ4 : ℚ,
      (∀ (v v' : InvVertex) (κ : Int), v.j ≤ 9 → v'.j ≤ 9 →
          InvKappaPreciseEdge 24 v v' κ →
          PhiHyb θ0 θ1 θ2 θ3 θ4 v ≤ (κ : ℚ) + PhiHyb θ0 θ1 θ2 θ3 θ4 v') ∧
      (∀ v : InvVertex, InvVertex.IsGoal v 24 → v.j ≤ 9 →
          PhiHyb θ0 θ1 θ2 θ3 θ4 v ≤ 0) ∧
      ((1 : ℚ) ≤ PhiHyb θ0 θ1 θ2 θ3 θ4 (InvStart 1)) := by
  rintro ⟨θ0, θ1, θ2, θ3, θ4, h_edge, h_goal, h_start⟩
  rw [show InvStart 1 = (⟨0, 31381059610⟩ : InvVertex) from by decide,
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 0 31381059610 35 22 0
        (by decide) (by decide) (by decide)] at h_start
  have hG := h_goal ⟨9, 1⟩ rfl (by decide)
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 9 1 1 33 0
        (by decide) (by decide) (by decide)] at hG
  have hE1 := h_edge _ _ _ (by decide) (by decide) hybB_edge1
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 3 4871909504303 43 0 3
        (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 4 7307864256455 43 0 4
        (by decide) (by decide) (by decide)] at hE1
  have hE2 := h_edge _ _ _ (by decide) (by decide) hybB_edge2
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 9 4975302956326384 53 1 0
        (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 9 310956434770399 49 1 0
        (by decide) (by decide) (by decide)] at hE2
  have hE3 := h_edge _ _ _ (by decide) (by decide) hybB_edge3
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 9 2462147789600812 52 1 0
        (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 9 615536947400203 50 8 0
        (by decide) (by decide) (by decide)] at hE3
  have hE4 := h_edge _ _ _ (by decide) (by decide) hybB_edge4
  rw [PhiHyb_eval θ0 θ1 θ2 θ3 θ4 8 1493722122425261 51 0 9
        (by decide) (by decide) (by decide),
      PhiHyb_eval θ0 θ1 θ2 θ3 θ4 9 1120291591818946 50 1 0
        (by decide) (by decide) (by decide)] at hE4
  push_cast at h_start hG hE1 hE2 hE3 hE4
  linarith

end CollatzLean4.Admissible
