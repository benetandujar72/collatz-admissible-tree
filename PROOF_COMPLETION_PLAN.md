# Proof-Completion Roadmap — Andújar Admissible Inverse Tree (κ-barrier sub-route)

> **Scope discipline.** This document is an *honest* dependency map, not a victory
> lap. Every rung is tagged `PROVEN` / `FORMALIZABLE-NOW` / `OPEN-NUMBER-THEORY` /
> `EXTERNAL`. Reductions are labelled as reductions, never as proofs. Where a
> theorem name appears it has been read in the source and its status verified.

---

## 1. TL;DR (read this first)

The Lean development formalizes the **κ-precise slope-barrier sub-route** of the
S202 alternative. Concretely, it proves — *unconditionally and machine-checked* —
that a Bellman–Ford closure certificate over the κ-weighted inverse-cylinder graph
implies the cylinder-accessibility barrier `defect ≥ m` for admissible words with
at most `Q` zero-steps (`S202_slope_barrier_from_kappa_cert`, non-circular). The
barrier currently holds **unconditionally only for `m = 1`** (per-instance
`native_decide` certificates `Cert_m1_Q{1,3,5,8,10}`), plus a weak
**uniform-in-`(m,Q)`** baseline `defect ≥ −Q + 1` (`analyticBarrier_for_words`).

A **2026-05-29 closing pass** (verified, 0 sorry, axiom-clean) added three pieces
on the analytic route: (i) the **one-edge discrete-log law `oneEdge_rhoPlus_law`**,
completing the ρ₊ edge calculus for *all four* edge types; (ii) the **correct
lifting-the-exponent closed form** `ν₃(2^S − 1) = (Even S ? 1 + ν₃(S) : 0)`
(`padicValNat_two_pow_sub_one`) plus the capped/uncapped bridge
`nu3_eq_padicValNat_of_lt`; and (iii) **Part A slackness** — unconditionally,
`ν₃(2^A − 1) = 22 ⟹ A ≥ 2·3^21 = 20 920 706 406` (`slackness_at_22`). The
prior pass had added the **3-unit invariance lemma `nu3_unit_mul`** and the
**τ=2 "clean climb" law `zeroEdge_tau2_rhoPlus_climb`**, completing the verified
ρ₊ transition table on zero-edges `{τ=1 reset ✓, τ=2 climb ✓, τ=3 reset ✓}`.
With law (1) now also proven, the ρ₊ transition table is **complete on every
edge type**, and the LTE engine is in place — but the **word→valuation bridge**
(`CylinderForcesVal22`) that would feed Part A from a cylinder condition was the
residual frontier (see §3.7).

A **2026-05-29 bridge-attack pass** (verified, 0 sorry, axiom-audited) has now
*resolved that frontier — negatively*. The bridge `CylinderForcesVal22` is
**FALSE as stated**, and the falsity is machine-checked (`BridgeTruth.lean`,
`cylinderForcesVal22_false_raw` / `_faithful`). The decisive counterexample is
the program's **own** witness, the S202 triple `(n,A,q,B) =
(251,43,22,919447060349)`: it satisfies the translation identity `3^q·n+B=2^A`
and the resonance `B≡2^A (mod 3^q)` exactly, and carries the cylinder's `22`
signature on the *n*-side (`ν₃(aS202−1)=22`, and indeed `ν₃(2^A−B)=22=q`), yet
`A=43` is **odd** so `ν₃(2^43−1)=0`, not `22`. The true relationship the pass
*did* prove (all axiom-clean): the only valuation the word semantics supplies is
the **resonance** `ν₃(2^A−B)=q` (subtraction constant `B`, **not** `1`), and in
the deep cylinder regime `q≥k` the identity **collapses** to `2^A≡B (mod 3^k)` —
so the cylinder residue of `n` is *annihilated* and places **no** constraint on
`2^A mod 3^k`, while `ν₃(2^A−1)` depends on `A` *alone* (parity + `ν₃(A)`). The
LTE/discrete-log route from the cylinder to `ν₃(2^A−1)` is therefore **blocked at
the level of the underlying number theory, not merely unproven**. Part A
(`slackness_at_22`) survives as a true *standalone* fact about the function
`ν₃(2^A−1)`, whose hypothesis is simply **unreachable** from the cylinder.

A **2026-05-30 KappaPathSplit pass** (verified, 0 sorry, axiom-audited) pivots to
the *other* uniform-`m` route — the committed `WPath`-split core
`KappaPathSplit m Q` itself (UniformBarrier.lean), independent of the dead LTE
bridge. It proves the **R2 brick**: a κ-preserving precision-reduction **functor**
`projπ` that lifts a level-`(m+1)` κ-path to a level-`m` κ-path of the *same* κ
(`InvKappaPreciseEdge_projectDown`, `WPath_projectDown`, `kappaProjectsDown_holds`,
`KappaSplitWork.lean`), discharging R2's precision-tower step as a theorem. The
same pass **sharpens the obstruction** rather than closing the core:
`IsGoal_projectDown_not_reflects` proves `projπ` is many-to-one (witness
`⟨0,1+3^24⟩`), so a projected prefix at an `m`-goal does **not** pin down the
level-`(m+1)` split point `mid` — a second, independent witness (beside
`kappa_no_canonical_depth_cut`) that `mid` is the genuine crux. A flagged
**Caveat C** (`InvStart` is the wrong cylinder for `m ≥ 2` until migrated to
`aS202_at m`) gates any non-toy use. `KappaPathSplit` is thus **reduced, not
proven**; its hard residue is the split point plus the `InvStart` migration.

**This is NOT a proof of Collatz, nor even of the full S202 alternative.** It is one
half (the slope-barrier half) of one branch of the S202 alternative, and it is
currently *uniform only for the toy index `m = 1`*. Reaching Collatz additionally
requires: (Level 1) the S202 alternative fully resolved **including** the
subcritical-access branch, and (Level 0) the **external "Bandujar reduction"**
connecting the S202 alternative to actual Collatz counterexamples. Neither is
formalized; the reduction is a non-formalizable mathematical claim *outside* this
program's current verified perimeter.

---

## 2. Dependency ladder — Level 4 → Level 0

The ladder runs from concrete machine-checked facts (Level 4) up to the Collatz
conjecture (Level 0). **An honest reader stops believing at the first
`OPEN`/`EXTERNAL` rung** — everything above that line is conditional on it.

| Level | Claim | Status | Pinned to |
|------:|-------|--------|-----------|
| **4** | ρ₊ transition table — **all four edge types**: zero-edge τ=1 reset / **τ=2 climb** / τ=3 reset, **and the one-edge discrete-log law**; 3-unit invariance + residue-congruence of ν₃ | **PROVEN** | `nu3_unit_mul`, `nu3_congr_mod_pow`, `zeroEdge_tau2_rhoPlus_climb`, `zeroEdge_tau_1/3_deltaPlus_max`, **`oneEdge_rhoPlus_law` (new 05-29)** |
| **4-LTE** | Lifting-the-exponent closed form `ν₃(2^S−1) = (Even S ? 1+ν₃(S) : 0)`; capped↔uncapped bridge; Part-A slackness `ν₃(2^A−1)=22 ⟹ A ≥ 2·3^21` | **PROVEN** (05-29) | `padicValNat_two_pow_sub_one`, `nu3_eq_padicValNat_of_lt`, `slackness_at_22`, `slackness_at_22_value` |
| **4-truth** | **True word structure** (replaces the false bridge): resonance `B≡2^A (mod 3^q)`; deep-regime **collapse** `q≥k ⟹ 2^A≡B (mod 3^k)` (cylinder residue of `n` annihilated); root valuation `ν₃(2^A−B)=q`; decoupling `ν₃(2^A−1)` depends on `A` alone | **PROVEN** (new 05-29) | `resonance_B_eq_two_pow`, `deep_regime_cylinder_collapse`, `defect_at_root_valuation`, `nu3_two_pow_sub_one_depends_only_on_A`, `cylinder_true_structure` |
| **3** | κ-precise edge calculus: weight trichotomy, path decomposition `defect ≥ n_one − n_neg`, slice telescoping, j-monotonicity, exact-count predicate | **PROVEN** | `invEdge_weight_trichotomy`, `WPath_weight_decompose`, `InvPathCounts.*`, `WPath_kappa_*` |
| **2** | **Reduction**: an `AbsCert`/closure certificate (or finite-slice κ-potential) over `InvKappaPreciseEdge` ⟹ `S216BarrierForWords m Q m`. Non-circular (counts pinned via `InvPathCounts`). | **PROVEN** (the *implication*) | `S202_slope_barrier_from_kappa_cert`, `S216_barrier_for_words_via_kappa`, `S202_slope_barrier_from_kappa_precise_potential_bounded` |
| **2′** | The certificate's hypothesis **discharged unconditionally** for `m = 1`, `Q ∈ {1,3,5,8,10}` | **PROVEN** (`native_decide`) | `Cert_m1_Q{1,3,5,8,10}_kappa.barrier_*` |
| **2-split** | **The `WPath`-split route to uniform-`m`**: `KappaPathSplit m Q` (prefix-κ ≥ `m`, suffix-κ ≥ `1`) + the `m=1` base ⟹ `defect ≥ m` for all `m`. THE single committed open core. | **OPEN** (the genuine crux: split point `mid`) | `KappaPathSplit`, `uniform_slope_barrier_of_cert_and_split` (UniformBarrier.lean) |
| **2-split-R2** | R2 brick: the κ-preserving precision-reduction **functor** `projπ` lifts a level-`(m+1)` κ-path to a level-`m` κ-path (same κ), discharging R2's precision-tower step | **PROVEN** (new 05-30) | `InvKappaPreciseEdge_projectDown`, `WPath_projectDown`, `kappaProjectsDown_holds` (KappaSplitWork.lean) |
| **2-bridge** | **Word→valuation bridge**: a cylinder condition `n ≡ aS202 (mod 3^24)` forces `ν₃(2^A−1)=22` (would have fed Part-A slackness into the κ counting) | **REFUTED — FALSE as stated** (machine-checked; blocked at the number-theory level, not merely unproven) | `cylinderForcesVal22_false_raw` / `_faithful`; counterexample = S202 triple; conditional corollary `cylinder_forces_astronomical_A` still typechecks but is **vacuously gated** by a false hypothesis |
| **2″** | The certificate's hypothesis discharged **uniformly in `m`** (one analytic Φ, not a per-`m` BFS table) | **OPEN-NUMBER-THEORY** | *target of §3 DAG* |
| **1a** | S202 slope-barrier branch: `defect ≥ m` for **all** `m` (uniform) | **OPEN-NUMBER-THEORY** | from 2″ (analytic Φ) **OR** Level 2-split (`KappaPathSplit` + m=1 base) |
| **1b** | S202 alternative *fully* resolved (slope barrier **and** subcritical-access branch) | **OPEN-NUMBER-THEORY** | 1a + an unformalized second branch |
| **0** | Bandujar reduction: "S202 alternative ⟹ no Collatz counterexample", then Collatz | **EXTERNAL** (not formalized; not in repo as a proof) | — |

**Where the honesty line sits:** everything through **Level 2′** (plus the new
Levels 4-LTE and 4-truth) is genuinely machine-checked. The **word→valuation
bridge** (Level 2-bridge) is **no longer an open gap — it is a closed, negative
result:** `CylinderForcesVal22` is *false*, machine-checked on the program's own
S202 witness, and the obstruction is structural (the cylinder controls `n mod
3^24`; `2^A` is a 3-adic unit and `ν₃(2^A−1)` lives on the orthogonal `A`-axis).
Consequently Part-A slackness, though *unconditional*, has a hypothesis that is
**unreachable from any cylinder word** — its astronomical conclusion `A ≥ 2·3^21`
never bites along this route. The first *remaining* real mathematical gaps are
**Level 2″ / 1a** (a uniform 3-adic argument — the genuine open dynamics, now
known to be **separate from** the dead LTE/dlog route). Levels **1b** and **0**
are *additional* gaps, the last of which is outside the formal program entirely.

The 2026-05-30 pass added a **second, parallel route into Level 1a** — the
committed `WPath`-split core `KappaPathSplit` (**Level 2-split**) — and discharged
its R2 sub-brick (**Level 2-split-R2**, the `projπ` precision functor) as a
machine-checked theorem. This does **not** move the honesty line: Level 2-split
itself is still OPEN, its crux being the non-constructible split point `mid`
(`IsGoal_projectDown_not_reflects` now gives a concrete many-to-one witness that
`mid` cannot be recovered from the projection alone), with `InvStart` migration
(Caveat C) as a prerequisite for `m ≥ 2`.

A weaker but **fully uniform** rung also exists and is proven:
`analyticBarrier_for_words : S216BarrierForWords m Q (−Q + 1)` for all `m ≥ 1, Q`.
It beats the trivial baseline `−Q` by exactly 1 but is far short of `defect ≥ m`.

### The proven chain, at a glance

```
Level 0  Collatz conjecture
   ▲ EXTERNAL  (Bandujar reduction — not formalized)
Level 1b  S202 alternative fully resolved
   ▲ OPEN     (+ subcritical-access branch, not formalized)
Level 1a  defect ≥ m  for all m   (uniform slope barrier)
   ▲ OPEN     (reachable via EITHER Level 2″ OR Level 2-split below)
   ├─────────────────────────────┐
Level 2-split  KappaPathSplit m Q  (prefix-κ≥m ∧ suffix-κ≥1) + m=1 base
   ┊ OPEN  ── crux = the split point `mid` (no canonical depth cut)
   ┊  R2 brick PROVEN (05-30): projπ precision functor lifts (m+1)-κ-path
   ┊          ↦ m-κ-path, same κ (InvKappaPreciseEdge_projectDown / WPath_projectDown);
   ┊          but IsGoal_projectDown_not_reflects ⇒ projπ many-to-one, mid NOT pinned;
   ┊          Caveat C: InvStart wrong cylinder for m≥2 until migrated to aS202_at m
Level 2″  uniform-in-m κ certificate / analytic Φ
   ┊ OPEN  ── ρ₊ edge calculus COMPLETE (all 4 laws); LTE engine in place,
   ┊          but now known to be SEPARATE from the (dead) cylinder→ν₃ route
Level 2-bridge  cylinder ⟹ ν₃(2^A−1)=22   (CylinderForcesVal22)
   ✗ REFUTED ── FALSE as stated; machine-checked on the S202 witness
   ✗          (cylinderForcesVal22_false_raw/_faithful). Route BLOCKED.
Level 4-truth  TRUE word structure: resonance B≡2^A(3^q); collapse
   ▲ PROVEN     q≥k⟹2^A≡B(3^k) (cylinder residue of n annihilated);
   ▲ (05-29)    root valuation ν₃(2^A−B)=q; ν₃(2^A−1) depends on A alone
Level 4-LTE  ν₃(2^A−1) closed form + Part-A slack A≥2·3^21   ✅ (05-29)
   ▲ PROVEN  (unconditional STANDALONE fact; hypothesis UNREACHABLE from cylinder)
Level 2′  defect ≥ 1   (m=1, Q∈{1,3,5,8,10})           ✅ native_decide
   ▲ PROVEN
Level 2   κ-cert  ⟹  S216BarrierForWords m Q m          ✅ non-circular
   ▲ PROVEN
Level 3   κ-edge calculus + path decomposition           ✅
   ▲ PROVEN
Level 4   ρ₊ transition table (all 4 edge types) + ν₃ unit/residue   ✅
```

---

## 3. Formalizable-lemma DAG (the part we can actually close in Lean now)

These are ordinary number-theory / dynamics lemmas that need no new external
input. They feed the **analytic uniform-`m` potential** (Level 2″), the single
most leveraged open target — now to be reached via the **additive-defect** bound
`A − 2q ≥ m`, since the LTE/discrete-log branch into the cylinder dead-ends at the
**refuted** bridge (bottom of DAG). Status reflects the current repo.

```
nu3_unit_mul ✅ ─────────────┐
                             ├──► oneEdge_rhoPlus_law ✅ (law 1, discrete-log, DONE 05-29)
nu3_congr_mod_pow ✅ ────────┤        │
                             │        ▼
nu3_mul_three ✅ ────────────┼──► zeroEdge_tau2_rhoPlus_climb ✅ (law 2, DONE)
                             │     ⇒ ρ₊ EDGE CALCULUS COMPLETE (all 4 laws)
nu3_eq_padicValNat_of_lt ✅ ─┴──► padicValNat_two_pow_sub_one ✅ ──► slackness_at_22 ✅
   (bridge, DONE 05-29)            (LTE closed form, DONE 05-29)      (Part A, STANDALONE ✅)
                                          │                              │
                                          │     ν₃(2^A−1)=22 ⟹ A≥2·3^21 (UNCONDITIONAL,
                                          ▼                              ▼  but hyp unreachable)
                                 CylinderForcesVal22  ✗✗✗ REFUTED — FALSE as stated ✗✗✗
                                 cylinderForcesVal22_false_raw/_faithful ✅ (machine-checked,
                                 counterexample = S202 triple (251,43,22,919447060349))
                                          ╳  no edge: the cylinder cannot reach ν₃(2^A−1)

  TRUE structure proven in its place (BridgeTruth.lean, all ✅, axiom-clean):
    resonance_B_eq_two_pow ──► deep_regime_cylinder_collapse ──► cylinder_true_structure
        (B≡2^A mod 3^q)          (q≥k ⟹ 2^A≡B mod 3^k;            (the honest replacement)
                                  n-residue annihilated)
    defect_at_root_valuation (ν₃(2^A−B)=q)   nu3_two_pow_sub_one_depends_only_on_A
        (the real valuation, of 2^A−B)            (ν₃(2^A−1) ⟂ cylinder, on A-axis)

  Level 2″ (uniform-in-m κ certificate / Φ) is reached by the ADDITIVE-DEFECT
  route (A−2q ≥ m via S216 / AnalyticBarrier), NOT by any LTE/ν₃(2^A−1) edge.
```

### 3.1 `nu3_unit_mul` — **PROVEN (prior pass)** ✅

```lean
theorem nu3_unit_mul (u x c : Nat) (hu : u % 3 ≠ 0) : nu3 (u * x) c = nu3 x c
```
The critical-path unblocker: the capped 3-adic valuation is invariant under
multiplication by a 3-unit. Induction on the cap `c` mirroring the `nu3`
recursion; the load-bearing step is `(u*x)/3 = u*(x/3)` via `Nat.mul_div_assoc`
(needs `3 ∣ x`). File: `Nu3UnitInvariance.lean`. Axioms: `{propext, Quot.sound}`.

### 3.2 `nu3_congr_mod_pow` — **PROVEN (prior pass)** ✅

```lean
theorem nu3_congr_mod_pow (c a b : Nat) (h : a % 3^c = b % 3^c)
    (ha : a ≠ 0) (hb : b ≠ 0) : nu3 a c = nu3 b c
```
The correct residue-transfer lemma. **Important correction to the original plan:**
the proposed `nu3_mod_pow : nu3 n c = nu3 (n % 3^c) c` is *false* at the
saturation residue `0` (e.g. `nu3 3 1 = 1` but `nu3 (3 % 3) 1 = nu3 0 1 = 0`,
because the `nu3 0 = 0` convention encodes "valuation 0", not "∞"). The
nonzero-hypothesis congruence form is the true and sufficient statement.

### 3.3 `zeroEdge_tau2_rhoPlus_climb` — **PROVEN (prior pass)** ✅ (law 2)

```lean
theorem zeroEdge_tau2_rhoPlus_climb {R} (hR : 1 ≤ R) {v v' ω}
    (h_zero : InvEdgeZero R v v' ω) (h_tau : tau v'.c = 2)
    (h_v_can : v.c < 3^(R+v.j)) (_ : v'.c < 3^(R+v'.j)) (h_v_ne1 : v.c ≠ 1) :
    rhoPlus v'.c (R+v'.j) = rhoPlus v.c (R+v.j) + 1
```
The τ=2 clean climb. Proof chain (main case `v'.c ≠ 1`):
`ρ₊(v'.c,r+1) = ν₃(v'.c−1) =[unit 4] ν₃(4(v'.c−1)) =[congr] ν₃(3(v.c−1))
=[nu3_mul_three] ν₃(v.c−1)+1 = ρ₊(v.c,r)+1`. Boundary `v'.c=1` via
`nu3_eq_cap_of_dvd`. Completes the zero-edge transition table.

### 3.4 `oneEdge_rhoPlus_law` (law 1, discrete-log) — **PROVEN 2026-05-29** ✅

```lean
theorem oneEdge_rhoPlus_law {R} (hR : 1 ≤ R) {v v' ω}
    (h_one : InvEdgeOne R v v' ω)
    (h_v'_can : v'.c < 3 ^ (R + v'.j)) (h_v'_ne1 : v'.c ≠ 1) :
    rhoPlus v'.c (R + v'.j)
      = nu3 ((v.c + (3 ^ (R + v.j) - 2 ^ tau v'.c % 3 ^ (R + v.j)))
              % 3 ^ (R + v.j)) (R + v.j)
```
Along a one-edge, `v'.c ≡ 2^{−τ}·v.c (mod 3^r)`, so `v'.c − 1 ≡ 2^{−τ}(v.c − 2^τ)`
and `2^{−τ}` is a 3-unit. Discharged with `oneEdge_threeUnit_inv` (the inverse
`invMod2Pow τ (3^r)` is a 3-unit), `oneEdge_discreteLog` (the inversion repackaged
from `outgoingEdges_complete_one`), then `nu3_congr_mod_pow` (residue transfer) +
`nu3_unit_mul` (strip the unit). File: `OneEdgeRhoLaw.lean`; axioms
`{propext, Classical.choice, Quot.sound}`.

**Documented form adjustment (not a gap):** the verified probe writes the RHS as
`ν₃((c − 2^τ) mod 3^r)` with **integer** subtraction. Since ℕ-subtraction
truncates when `v.c < 2^τ` (the hypotheses do not exclude this, and `v.c` need not
be canonical), the law renders the ℤ-residue faithfully as
`(v.c + (3^r − 2^τ mod 3^r)) mod 3^r`. This is the exact, always-correct ℕ
transcription — purely a representation choice, not a weakening. With this law
proven, the ρ₊ edge calculus is **complete on all four edge types**.

### 3.5 `nu3_eq_padicValNat_of_lt` — **PROVEN 2026-05-29** ✅

```lean
theorem nu3_eq_padicValNat_of_lt (n c : Nat) (hn : n ≠ 0)
    (hlt : padicValNat 3 n < c) : nu3 n c = padicValNat 3 n
```
One-directional bridge from the custom capped `nu3` to Mathlib's `padicValNat` in
the cap-not-binding regime (`nu3 n c = min(padicValNat 3 n, c)`; this is the
unsaturated case; the saturated case is already `nu3_eq_cap_of_dvd`, S214Core:278).
Induction on `c` against `padicValNat.div` / `padicValNat.eq_zero_of_not_dvd`;
`Fact (Nat.Prime 3)` found automatically. File: `LTEBound.lean`; axioms clean.
**Leverage realised:** with `nu3 = padicValNat` in the astronomically-sub-`3^21`
regime, Mathlib's lifting-the-exponent now applies to the project's `nu3` for free
— this is the gateway that made §3.6 mechanical.

### 3.6 `padicValNat_two_pow_sub_one` (LTE core) — **PROVEN 2026-05-29** ✅ (with corrected statement)

```lean
theorem padicValNat_two_pow_sub_one (S : Nat) (hS : S ≠ 0) :
    padicValNat 3 (2^S - 1) = if Even S then 1 + padicValNat 3 S else 0
```
**Correction to the original plan:** the proposed `ν₃(2^S − 1) = ν₃(S)` is
**WRONG**. Because `3 ∤ (2 − 1) = 1`, Mathlib's odd-prime LTE lemma
`padicValNat.pow_sub_pow` cannot be applied to base `2` directly; one must reindex
through `2^{2t} = 4^t` (so `3 ∣ 4 − 1 = 3`) and split on parity. The **even
branch carries a `+1`** the naive guess missed; the odd branch is `0` (since
`2^S ≡ 2 mod 3`). Supporting lemmas in `LTEBound.lean`:
`padicValNat_four_pow_sub_one` (`ν₃(4^t−1)=1+ν₃(t)`),
`padicValNat_two_pow_sub_one_even`, `padicValNat_two_pow_sub_one_odd`. All axioms
clean. This is the quantitative engine behind §3.7 (Part A) — and, via its
`A`-only form, the proof that `ν₃(2^A−1)` is **decoupled** from the cylinder
(`nu3_two_pow_sub_one_depends_only_on_A`, the heart of the §3.7B refutation).

### 3.7 Part-A slackness ✅ (STANDALONE) → `CylinderForcesVal22` ✗ REFUTED → true structure proven

The payoff chain, now **split into a proven standalone half and a REFUTED bridge**
(`BarrierSlack.lean` + `BridgeTruth.lean`):

**Part A — UNCONDITIONAL, fully proven, but STANDALONE.** From the LTE closed
form (§3.6):
```lean
theorem slackness_at_22 {A} (hA : A ≠ 0) (hval : padicValNat 3 (2^A - 1) = 22) :
    2 * 3 ^ 21 ≤ A        -- = 20 920 706 406 ≈ 2.09 × 10^10
```
plus `even_of_valuation_two_pow_sub_one_pos`, `dvd_of_valuation_two_pow_sub_one`
(`ν₃(2^A−1)=v≥1 ⟹ 2·3^(v−1) ∣ A`), `slackness_from_valuation`,
`slackness_at_22_value`. The constant `22` is structurally correct *as a fact
about the cylinder centre*: `padicValNat_aS202_sub_one : ν₃(aS202 − 1) = 22`
(from `aS202 − 1 = 3^22`). **But (see Part B) the hypothesis `ν₃(2^A−1)=22` is
unreachable from any cylinder word**, so this lemma is now documented as a true
standalone arithmetic fact, *not* a live lower bound on word-`A`.

**Part B — the word→valuation bridge: REFUTED, FALSE as stated.** The hoped-for
step was to *derive* `ν₃(2^A − 1) = 22` from the cylinder condition. It was
isolated as a named hypothesis (never an `axiom`):
```lean
def CylinderForcesVal22 : Prop :=
  ∀ u : Word, (evalWord u).n % 3^24 = aS202 % 3^24 → (evalWord u).A ≠ 0 →
    padicValNat 3 (2 ^ (evalWord u).A - 1) = 22
```
The 2026-05-29 bridge-attack pass **disproved it** (machine-checked,
`BridgeTruth.lean`):
```lean
theorem cylinderForcesVal22_false_raw :       -- weakest-hypothesis form
  ¬ (∀ A q B n, 3^q*n+B = 2^A → B % 3^q = 2^A % 3^q → A ≠ 0 →
       padicValNat 3 (2^A - 1) = 22)
theorem cylinderForcesVal22_false_faithful :  -- + the cylinder's ν₃(2^A−B)=22 signature
  ¬ (∀ A q B n, 3^q*n+B = 2^A → B % 3^q = 2^A % 3^q →
       padicValNat 3 (2^A - B) = 22 → A ≠ 0 → padicValNat 3 (2^A - 1) = 22)
```
**Counterexample = the program's own witness.** The S202 triple
`(n,A,q,B)=(251,43,22,919447060349)` satisfies the translation identity and the
resonance exactly, and carries the `22` signature on the *n*-side
(`ν₃(2^A−B)=22=q`), yet `A=43` is odd so `ν₃(2^43−1)=0≠22`
(`nu3_two_pow_AS202_sub_one`, `nu3_two_pow_AS202_sub_BS202`,
`AS202_valuations_differ`). The conditional corollary
`cylinder_forces_astronomical_A` still typechecks, but it is now **vacuously
gated by a false hypothesis** and yields nothing.

**Why the route is BLOCKED (structural, not a missing proof).** The translation
identity `3^q·n + B = 2^A` yields exactly one valuation fact — the resonance
`ν₃(2^A − B) = q`, with subtraction constant **B, not 1**. In the deep cylinder
regime (`q ≥ k`, and the `m=1` cylinder needs `k=24, q≥22`) it *collapses* to
`2^A ≡ B (mod 3^k)`: the `n`-term `3^q·n` is annihilated mod `3^k`, so the
cylinder residue of `n` **drops out** and constrains `2^A mod 3^k` not at all.
Meanwhile `2^A` is a 3-adic **unit** (`ν₃(2^A)=0`) and `ν₃(2^A − 1)` is a
function of **`A` alone** (parity + `ν₃(A)`) — an orthogonal axis the cylinder
never touches. There is no implication to repair; the LTE/discrete-log route to
`ν₃(2^A − 1)` is genuinely dead.

**The true structure proven in its place** (`BridgeTruth.lean`, all 0 sorry):
`resonance_B_eq_two_pow` (B≡2^A mod 3^q), `deep_regime_cylinder_collapse`
(q≥k ⟹ 2^A≡B mod 3^k), `defect_at_root_valuation` (n=1 ⟹ ν₃(2^A−B)=q),
`nu3_two_pow_sub_one_depends_only_on_A`, and the bundled
`cylinder_true_structure`. These are the honest replacement for the false bridge.

**Consequence for the program.** Retire `CylinderForcesVal22`; reframe
`BarrierSlack` Part B around the **additive defect** bound `A − 2q ≥ m` that the
inverse-graph potential (S216 / `AnalyticBarrier`) genuinely supplies — that
route carries no multiplicative `ν₃(2^A−1)` content and is the live path to
Level 2″/1a. Even there, a uniform `defect ≥ m for all m` still requires a
per-word lower bound on `n_one`, the genuine open dynamics. So 2″/1a remain OPEN,
but the *path* to them no longer runs through the (dead) LTE/dlog bridge.

### Ranked next steps (highest leverage first)

The previous frontier item — discharge `CylinderForcesVal22` — is **closed
negatively** (refuted, 05-29). The LTE/dlog bridge route is dead. **Note (05-30):**
this DAG is the *analytic-Φ* route; a **parallel** route now exists — the committed
`WPath`-split `KappaPathSplit` (Level 2-split, §5.-1), whose R2 brick is proven.
The two below are the highest-leverage items *on the analytic route*; the
split-route frontier (`InvStart` migration → split point `mid` / R1) is ranked in
§5.-1 and the document summary.

1. **Analytic Φ from the now-complete ρ₊ edge calculus (Level 2″) via the
   ADDITIVE-DEFECT bound.** Attempt a finite-slice κ-potential `Φ` uniform in `m`
   feeding `S202_slope_barrier_from_kappa_precise_potential_bounded`, built on
   `A − 2q ≥ m` (`AnalyticBarrier`), **not** on `ν₃(2^A−1)`. Highest-leverage open
   target **on the analytic route**. The ρ₊ laws and LTE engine remain valid
   infrastructure; they simply do not connect to the cylinder via `ν₃(2^A−1)`.
2. **A uniform lower bound on `n_one` per admissible word** — the common core the
   additive route ultimately needs for `defect ≥ m for all m` (Level 1a).
3. **Housekeeping:** mark `slackness_at_22` in `BarrierSlack.lean` as a standalone
   fact and either delete `CylinderForcesVal22` /
   `cylinder_forces_astronomical_A` or annotate them as referencing a
   *refuted* hypothesis (cross-reference `BridgeTruth.lean`), so no future reader
   mistakes the conditional corollary for a live result.

---

## 4. External / non-formalizable gaps (the parts no Lean lemma closes)

These are tagged `EXTERNAL` because they are *mathematical* claims about Collatz
itself, not statements internal to the inverse-tree formalism. **None is proven;
none is conjecturally close.**

- **G0 — The Bandujar reduction (Level 0).** The asserted implication
  "S202 alternative holds ⟹ Collatz has no nontrivial cycle / no divergent
  orbit." This is the bridge from the entire inverse-cylinder program to the actual
  Collatz dynamics. It is **not in the repository as a proof**, and formalizing it
  would require formalizing the accelerated-Collatz ↔ admissible-word correspondence
  at full strength. Treat as an open external hypothesis.

- **G1 — The subcritical-access branch (Level 1b).** The S202 *alternative* is a
  disjunction; this document's machinery attacks only the **slope-barrier**
  disjunct. The complementary **subcritical-access** branch (that the subcritical
  region cannot be entered/escaped in the relevant way) is **not formalized** and
  not addressed by the κ route. Even a complete uniform `defect ≥ m` leaves this
  branch fully open.

- **G2 — Uniformity in `m` (Level 2″/1a).** *Technically* number-theoretic rather
  than external, but worth flagging beside the externals because it is the gate to
  any non-toy claim: the proven barrier is **unconditional only for `m = 1`**. The
  per-instance certificates are `native_decide` BFS tables; there is **no** single
  analytic certificate valid for all `m`. The §3 DAG's *infrastructure* is
  complete (the four ρ₊ edge laws and the LTE engine are all proven as of 05-29),
  but the load-bearing dynamical input — a per-word lower bound on `n_one`, fed
  into the **additive-defect** route `A − 2q ≥ m` — remains unproven, so G2 is
  still open. **Note (05-29):** the one-time hope of routing G2 through the
  cylinder→`ν₃(2^A−1)` bridge (G3) is now **eliminated** — that bridge is refuted
  (below). G2 must be approached additively, not via LTE.

- **G3 — The word→valuation bridge (Level 2-bridge): NOW REFUTED, not open.**
  The 05-29 pass attempted, and **disproved**, the implication
  `cylinder n ≡ aS202 (mod 3^24) ⟹ ν₃(2^A − 1) = 22`. It was the named `Prop`
  `CylinderForcesVal22` (a hypothesis, never an axiom); it is **FALSE as stated**,
  machine-checked via `cylinderForcesVal22_false_raw` / `_faithful` in
  `BridgeTruth.lean`, with the program's own S202 triple
  `(251,43,22,919447060349)` as counterexample (identity + resonance + `22`
  signature all hold, yet `A=43` odd ⟹ `ν₃(2^43−1)=0`). The obstruction is
  structural and decisive: `2^A` is a 3-adic unit and `ν₃(2^A−1)` depends on `A`
  alone, while the deep-regime collapse `2^A ≡ B (mod 3^k)` annihilates the
  cylinder residue of `n`. G3 is therefore **discharged as a negative result**:
  there is nothing left to prove here, and the LTE/dlog slope-barrier route is
  blocked. The true facts that *do* hold are recorded in `BridgeTruth.lean`
  (resonance, collapse, root valuation, decoupling).

> If anyone summarizes this work as "proved Collatz", "proved the S202
> alternative", or "proved `defect ≥ m`", that is an **overclaim**. The defensible
> statement is: *"machine-checked, non-circular reduction of the S202 slope-barrier
> sub-route to a κ-weighted closure certificate, discharged unconditionally for
> `m = 1`; the ρ₊ transition table is complete on all four edge types and the
> lifting-the-exponent slackness `ν₃(2^A−1)=22 ⟹ A ≥ 2·3^21` is proven
> unconditionally as a standalone arithmetic fact. The hoped-for word→valuation
> bridge `CylinderForcesVal22` that would have made that slackness bite on word-`A`
> is now **machine-checked FALSE** (refuted on the program's own S202 witness): the
> LTE/discrete-log route from the cylinder to `ν₃(2^A−1)` is structurally blocked,
> and the true word structure (resonance `ν₃(2^A−B)=q`, deep-regime collapse,
> `A`-only decoupling) is recorded instead. The uniform-`m` barrier (to be pursued
> via the additive-defect route, not LTE), the subcritical-access branch, and the
> external Bandújar reduction all remain open."*

---

## 5. Change log (verified passes)

### 5.-1 KappaPathSplit R2-functor pass — 2026-05-30 (verified, axiom-audited)

**This pass changed attack target.** All prior passes (§5.0–5.2) attacked the
*analytic* uniform-`m` route (ρ₊ edge calculus, LTE, the cylinder→`ν₃(2^A−1)`
bridge). That route is sound infrastructure but its slope-barrier branch
dead-ended at the refuted bridge (§5.0). **This pass instead attacks the actual
committed open core `KappaPathSplit m Q`** (UniformBarrier.lean) directly — the
`WPath` split whose decomposition into prefix-κ ≥ `m` and suffix-κ ≥ `1` would,
together with the `m=1` base κ-cert, yield `defect ≥ m` for all `m` via the
committed `uniform_slope_barrier_of_cert_and_split`.

One new file, namespace `CollatzLean4.Admissible`, **0 sorry**, built clean
against cached Mathlib (`lake build CollatzLean4.KappaSplitWork` → 3324 jobs,
exit 0, **8.4s** cached replay; **independently re-run and reconfirmed here**;
NO `Cert_m1_Q10` blow-up; only the specific module was built; root aggregator
untouched):

- `CollatzLean4/CollatzLean4/KappaSplitWork.lean` (imports only `UniformBarrier`,
  hence `AnalyticBarrier`/`InverseGraph`/`AS202Lift` transitively)

**What was proven (the R2 brick).** `KappaPathSplit`'s docstring splits its proof
into **R1** (suffix κ₂ ≥ 1, the outermost `wS202` block forces a net one-edge)
and **R2** (prefix κ₁ ≥ m, the inner path *projected from precision `22(m+1)+2`
down to `22m+2`* carries the m-level barrier). R2 needs a κ-preserving
precision-reduction map lifting a level-`(m+1)` κ-path to a genuine level-`m`
κ-path so the IH barrier `S202_kappa_precise_barrier_bounded m Q` can apply. This
pass **builds and verifies exactly that functor** — the one unconditionally-true,
`native_decide`-free brick in this neighbourhood.

| Lemma | Statement | Role |
|---|---|---|
| `projπ` | `projπ m ⟨j,c⟩ := ⟨j, c % 3^(22m+2+j)⟩` | The precision-reduction map (R2's missing functor): keep depth `j`, drop digits between precision `22m+2+j` and `22(m+1)+2+j` |
| `descend_eq` | `a≡b (mod 3^(22(m+1)+2+j)) → a≡b (mod 3^(22m+2+j))` | Sole arithmetic core: smaller power divides larger |
| `descend_one_cons` / `descend_zero_cons` | one-/zero-edge `InvEdge` consistency clauses descend under `projπ` (zero-edge realigns `3·c+1` via `three_mul_mod_pow_succ`) | Edge-consistency descent |
| **`InvKappaPreciseEdge_projectDown`** | level-`(m+1)` κ-precise edge ↦ level-`m` κ-precise edge with the **same** κ | **THE CORE BRICK** — all three κ-classes preserved verbatim (`tau_mod_pow`/`InX_mod_pow` + descent helpers) |
| **`WPath_projectDown`** | level-`(m+1)` κ-path ↦ level-`m` κ-path, **same** total κ, vertices `vs.map (projπ m)` | Functoriality (induction on the path) |
| `IsGoal_projectDown` | level-`(m+1)` goal ↦ level-`m` goal | Goals descend |
| **`IsGoal_projectDown_not_reflects`** | `∃ m v, IsGoal (projπ m v) (22m+2) ∧ ¬IsGoal v (22(m+1)+2)` (witness `v=⟨0,1+3^24⟩`, m=1) | **THE HONEST OBSTRUCTION**: converse is FALSE; `projπ` is many-to-one |
| `projπ_InvStart` | `projπ m (InvStart (m+1)) = InvStart m` (m ≥ 1) | Start fixed point — **accident of the shared low-precision `aS202`** (Caveat C) |
| `KappaProjectsDown` / `kappaProjectsDown_holds` | named `Prop` "qualifying `(m+1)`-κ-path projects to an `m`-κ-path from `InvStart m` to an `m`-goal, same κ" + its **proof** (m ≥ 1) | R2's precision-tower step **discharged** as a theorem, removed from the open set |
| `kappaProjectsDown_preserves_kappa` | κ-invariance audit | The bound `(m:Int) ≤ κ` on the projected path *is* a bound on the original κ |

**The honest obstruction is part of the deliverable.** `IsGoal_projectDown_not_reflects`
is the formal reason R2 *reduces* but does **not close** `KappaPathSplit`: because
`projπ` is many-to-one, a projected prefix arriving at a level-`m` goal does **not**
pin down the level-`(m+1)` split point `mid`. This is precisely the obstruction the
committed `kappa_no_canonical_depth_cut` already records (the depth coordinate `j`
gives no canonical cut). So the split point `mid` remains the genuine crux — now
with a *second*, independent formal witness that it cannot be recovered cheaply.

**Caveat C (flagged, gating any `m ≥ 2` use).** `projπ_InvStart` holds **only**
because `InvStart k := ⟨0, aS202 % 3^(22k+2)⟩` reuses the single low-precision
constant `aS202 = 1+3^22 < 3^24`, so `InvStart k = ⟨0, aS202⟩` for every `k ≥ 1`.
By `aS202_at_2_ne_aS202_mod_3_46` (AS202Lift.lean) that constant is the **wrong**
S202 fixed-point cylinder for `m ≥ 2`. Hence `kappaProjectsDown_holds` is true *as
a statement about the graph objects `InvStart`*, but applying the IH barrier to
the projected prefix for `m ≥ 2` is **on sand** until `InvStart` migrates to the
coherent tower `aS202_at m`. This migration is a clean, `native_decide`-checkable
step that this pass did **not** perform.

**Axiom footprint (re-audited).** The pure functor/arithmetic core —
`InvKappaPreciseEdge_projectDown`, `WPath_projectDown`, `IsGoal_projectDown`,
`descend_eq`, `descend_one_cons`, `descend_zero_cons` — depends on **only**
`{propext, Quot.sound}` (a strict subset of the allowed set).
`IsGoal_projectDown_not_reflects` is `{propext, Classical.choice, Quot.sound}`.
The three `InvStart`-touching lemmas (`projπ_InvStart`, `kappaProjectsDown_holds`,
`kappaProjectsDown_preserves_kappa`) **additionally** pull in the pre-existing
`aS202_decomp._native.native_decide.ax_1_1` (the permitted aS202 `native_decide`
anchor, **not** introduced here). No `sorryAx`, no new custom axiom.

**Net effect on the ladder.** A new sub-rung **Level 2-split-R2** is proven (the
R2 precision-reduction functor). The monolithic open core `KappaPathSplit m Q` is
**reduced**, not closed: its residual content is now concentrated in (i) the split
point `mid` (R1 + the no-canonical-cut obstruction, now doubly witnessed), and
(ii) the `InvStart`-migration prerequisite for `m ≥ 2`. Levels 2″/1a/1b/0 are
**unchanged**. `KappaPathSplit`'s obstruction is now **sharper** (a concrete
many-to-one witness), not closer to discharge.

### 5.0 Bridge-attack pass — 2026-05-29 (verified, independently axiom-audited)

One new file, namespace `CollatzLean4.Admissible`, **0 sorry**, built clean
against cached Mathlib (`lake build CollatzLean4.BridgeTruth` → 3317 jobs, exit 0;
reproduced here):

- `CollatzLean4/CollatzLean4/BridgeTruth.lean` (imports `AdmissibleBasic`,
  `S202Cylinders`, `LTEBound`, `Defect`)

**Verdict on `CylinderForcesVal22`: FALSE as stated (machine-checked refutation).**
The bridge is not merely unproven — it is *disprovable*, and the disproof uses the
program's own S202 witness. The true relationship was discovered and formalized in
its place.

| Lemma | Statement | Role |
|---|---|---|
| `resonance_B_eq_two_pow` | `B ≡ 2^A (mod 3^q)` (re-export) | The **sole** valuation fact the translation identity yields |
| **`deep_regime_cylinder_collapse`** | `q ≥ k → 2^A ≡ B (mod 3^k)` | **The collapse:** cylinder residue of `n` annihilated; axiom-clean |
| `cylinder_residue_irrelevant_to_two_pow` | `q ≥ 24 → 2^A ≡ B (mod 3^24)` | `m=1` specialization: cylinder has zero leverage on `2^A` |
| `defect_at_root_valuation` | `n=1 → ν₃(2^A − B) = q` | The genuine valuation — of `2^A−B`, **not** `2^A−1` |
| `nu3_two_pow_sub_one_depends_only_on_A` | `ν₃(2^A−1) = (Even A ? 1+ν₃(A) : 0)` | Decoupling: lives on the `A`-axis, ⟂ cylinder |
| `nu3_two_pow_AS202_sub_one` | `ν₃(2^43 − 1) = 0` | Decisive half: the `2^A−1` side sees `0`, not `22` |
| `nu3_two_pow_AS202_sub_BS202` | `ν₃(2^43 − BS202) = 22` | The `22` really lives on `2^A−B` (`=3^22·251`) |
| `AS202_valuations_differ` | `ν₃(2^A−B) ≠ ν₃(2^A−1)` on S202 | Two genuinely different 3-adic objects |
| **`cylinderForcesVal22_false_raw`** | `¬(identity + resonance + A≠0 ⟹ ν₃(2^A−1)=22)` | **The refutation** (weakest-hypothesis form) |
| **`cylinderForcesVal22_false_faithful`** | as above **+** `ν₃(2^A−B)=22` signature | The maximally bridge-faithful refutation |
| `cylinder_true_structure` | resonance ∧ collapse, bundled | The honest replacement for the false bridge |

**Axiom footprint (independently re-checked via `#print axioms`).** The core
structural facts are clean: `deep_regime_cylinder_collapse`,
`cylinder_residue_irrelevant_to_two_pow`, `root_word_two_pow_sub_B`,
`defect_at_root_valuation`, `nu3_two_pow_sub_one_depends_only_on_A`,
`resonance_B_eq_two_pow`, `cylinder_true_structure` →
`{propext, Classical.choice, Quot.sound}` only. The headline refutation
`cylinderForcesVal22_false_raw` adds **only the pre-existing** S202 anchors
`S202_translation_identity._native`, `S202_resonance._native` (from `Defect.lean`,
not introduced here). *One new* `native_decide` axiom
`nu3_two_pow_AS202_sub_BS202._native` is introduced (proving
`2^43 − 919447060349 = 3^22·251`); it touches only
`nu3_two_pow_AS202_sub_BS202`, `AS202_valuations_differ`, and
`cylinderForcesVal22_false_faithful` — **not** the cleanest refutation
`_raw`, which therefore rests solely on the trusted pre-existing facts.

**Net effect on the ladder.** Level **2-bridge** flips from `OPEN-NUMBER-THEORY`
to **REFUTED** (a closed negative result). A new **Level 4-truth** rung is proven
(the real word structure). Levels 2″/1a/1b/0 are **unchanged** — but the *route*
to 2″/1a is now explicitly the **additive-defect** path (`A − 2q ≥ m`), with the
LTE/discrete-log slope-barrier route marked **dead**.

### 5.1 Closing pass — 2026-05-29 (verified, independently axiom-audited)

Three new files, all namespace `CollatzLean4.Admissible`, all **0 sorry**, all
built against cached Mathlib (~15s replays):

- `CollatzLean4/CollatzLean4/OneEdgeRhoLaw.lean` (imports `Nu3UnitInvariance`)
- `CollatzLean4/CollatzLean4/LTEBound.lean` (imports `Potential`,
  `Mathlib.NumberTheory.Multiplicity`, `…Padics.PadicVal.Basic`)
- `CollatzLean4/CollatzLean4/BarrierSlack.lean` (imports `LTEBound`, `S202Cylinders`)

Build commands: `lake build CollatzLean4.OneEdgeRhoLaw`,
`… CollatzLean4.LTEBound`, `… CollatzLean4.BarrierSlack` (run from `CollatzLean4/`).

| Lemma | Statement | Role |
|---|---|---|
| `oneEdge_threeUnit_inv` | `r≥1 → invMod2Pow τ (3^r) % 3 ≠ 0` | The inverse is a 3-unit (hypothesis for `nu3_unit_mul`) |
| `oneEdge_discreteLog` | `InvEdgeOne … → invMod2Pow τ M · v.c ≡ v'.c (mod M)` | Discrete-log inversion (repackaged from `outgoingEdges_complete_one`) |
| **`oneEdge_rhoPlus_law`** | `ρ₊(v',r) = ν₃((v.c + (3^r − 2^τ%3^r))%3^r)` | **Law (1)** — completes the ρ₊ edge calculus (all 4 types) |
| `padicValNat_four_pow_sub_one` | `t≠0 → ν₃(4^t−1)=1+ν₃(t)` | LTE base-4 (since `3∣4−1`) |
| **`padicValNat_two_pow_sub_one`** | `ν₃(2^S−1)= Even S ? 1+ν₃(S) : 0` | **Correct LTE closed form** (naive `ν₃(S)` was WRONG) |
| `nu3_eq_padicValNat_of_lt` | `padicValNat 3 n < c → nu3 n c = padicValNat 3 n` | Capped↔uncapped bridge (opens Mathlib LTE for `nu3`) |
| `dvd_of_valuation_two_pow_sub_one` | `ν₃(2^A−1)=v≥1 → 2·3^(v−1) ∣ A` | Part-A core (divisibility form) |
| **`slackness_at_22`** | `ν₃(2^A−1)=22 → A ≥ 2·3^21` | **Part A**: unconditional astronomical slack (`= 20 920 706 406`) |
| `CylinderForcesVal22` | `def : Prop` (cylinder ⟹ `ν₃(2^A−1)=22`) | Isolated here as a named hypothesis — **subsequently REFUTED, see §5.0** |
| `cylinder_forces_astronomical_A` | `bridge → … → A ≥ 2·3^21` | Conditional corollary (proven *given* the bridge — **now vacuous: hypothesis is false, §5.0**) |

**Axiom footprint (independently re-checked via `#print axioms`).** All headline
results — the one-edge law, the LTE closed form + bridge, Part-A slackness, and the
conditional bridge corollaries — depend on **only** `{propext, Classical.choice,
Quot.sound}`. *Caveat:* the two auxiliary "sanity anchors"
`padicValNat_aS202_sub_one` and `nu3_aS202_sub_one` additionally carry
`aS202_decomp._native.native_decide.ax_1_1` — the compiled-kernel-evaluation trust
axiom inherited transitively from the **pre-existing** `aS202_decomp`
(`S202Cylinders.lean:116`, `native_decide`). This was **not** introduced by this
pass and does not touch any headline lemma.

**Net effect on the ladder.** Level 4 is now complete on **all four** edge types
(law (1) joins the zero-edge table); a new **Level 4-LTE** rung is proven
unconditionally; and a new **Level 2-bridge** rung is *explicitly isolated*
(`CylinderForcesVal22`). It does **not** change Levels 2″/1a/1b/0 — the
uniform-`m` barrier, the subcritical branch, and the external reduction remain open
exactly as before. The frontier sharpened from "build the LTE engine" (done) to
"discharge the word→valuation bridge."

> **Superseded by §5.0 (later same day):** the bridge `CylinderForcesVal22`
> isolated here was *attacked and machine-checked FALSE* in the bridge-attack
> pass. The "frontier" framing above is retained as the historical state at the
> end of the closing pass; the live verdict is in §5.0 — the bridge is REFUTED and
> the slope-barrier route pivots to the additive-defect bound.

### 5.2 Prior pass — ρ₊ zero-edge table + ν₃ unit/residue lemmas (verified)

New file: `CollatzLean4/CollatzLean4/Nu3UnitInvariance.lean` (namespace
`CollatzLean4.Admissible`; imports `S214Core`, `RhoTransitionLaws`, `InverseGraph`).
Build: `lake build CollatzLean4.Nu3UnitInvariance` → clean, **0 sorry**, 0 errors.
Independently re-audited: `#print axioms` on all four theorems stays within
`{propext, Classical.choice, Quot.sound}` — **no `sorryAx`, no custom axioms**.

| Lemma | Statement | Role |
|---|---|---|
| `nu3_unit_mul` | `u%3≠0 → nu3 (u*x) c = nu3 x c` | **The critical-path unblocker** (3-unit invariance) |
| `nu3_congr_mod_pow` | `a%3^c=b%3^c → a≠0 → b≠0 → nu3 a c = nu3 b c` | Correct residue transfer (replaces the *false* `nu3_mod_pow`) |
| `mod9_of_tau_eq_two` | `tau n = 2 → n%9 ∈ {1,4}` | Helper for the climb's modular bookkeeping |
| `zeroEdge_tau2_rhoPlus_climb` | τ=2 zero-edge: `ρ₊(v',r+1) = ρ₊(v,r)+1` | **Law (2)**: completes `{τ=1 reset, τ=2 climb, τ=3 reset}` |

---

### Document summary (7 lines)

1. This is the κ-precise **slope-barrier sub-route**, explicitly *not* a Collatz proof; Ladder Levels 4→2′ are machine-checked and the κ-cert ⟹ `defect ≥ m` reduction is PROVEN/non-circular, but discharged unconditionally only for `m = 1`.
2. **Headline of the 2026-05-30 pass: the R2 brick of the committed open core `KappaPathSplit` is proven** — a κ-preserving precision-reduction **functor** `projπ` lifts a level-`(m+1)` κ-path to a level-`m` κ-path of the *same* κ (`InvKappaPreciseEdge_projectDown`, `WPath_projectDown`, `kappaProjectsDown_holds`; `KappaSplitWork.lean`, 0 sorry, built in 8.4s, no `Cert_m1_Q10`), discharging R2's precision-tower step as a theorem.
3. **The same pass sharpens the obstruction, it does not close the core:** `IsGoal_projectDown_not_reflects` proves `projπ` is many-to-one (witness `⟨0,1+3^24⟩`), so a projected prefix at an `m`-goal does NOT pin down the level-`(m+1)` split point `mid` — a second formal witness (beside `kappa_no_canonical_depth_cut`) that `mid` is the genuine crux. Flagged Caveat C: `InvStart` is the wrong cylinder for `m ≥ 2` until migrated to `aS202_at m`.
4. **Ladder update:** new sub-rungs **Level 2-split** (the `WPath`-split route, OPEN — crux = `mid`) and **Level 2-split-R2** (the functor, PROVEN 05-30); `KappaPathSplit` is **reduced, not closed**. (Prior 05-29: Level 2-bridge `OPEN → REFUTED`, new Level 4-truth; the LTE/dlog slope-barrier route stays dead.) Axiom audit: pure functor core on `{propext, Quot.sound}`; the three `InvStart`-touching lemmas add only the pre-existing `aS202_decomp._native` anchor; no `sorryAx`, no new custom axiom.
5. The κ-`WPath`-split route is now a **distinct, live alternative** to the analytic-Φ route into Level 1a; both remain OPEN, but the split route's residue is concentrated, locatable, and partly discharged (R2 done; R1 + split point + `InvStart` migration remain).
6. Levels 2″/1a (uniform-in-`m`), 1b (subcritical-access branch), 0 (Bandújar reduction) remain OPEN/EXTERNAL; the route to Collatz is **not materially advanced** — it is still gated behind the full `KappaPathSplit` (now reduced but with its crux untouched) and the external Bandújar reduction.
7. Single most valuable next formal step: **the `InvStart`-migration lemma** (`projπ m (InvStart (m+1)) = InvStart m` re-proven on the coherent tower `aS202_at m`, a clean `native_decide`-checkable step) — it lifts Caveat C and makes the proven R2 brick usable for `m ≥ 2`, the necessary precondition before any attack on the split point `mid` / R1 can rest on solid ground.
