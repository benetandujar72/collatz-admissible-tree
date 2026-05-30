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

A **2026-05-30 BlockBoundaryExists pass** (verified, 0 sorry, 0 axiom, independently
axiom-audited) advances to the *successor* committed core. The `KappaPathSplit`
residue of the prior pass has since been packaged as the single committed open Prop
**`BlockBoundaryExists m Q`** (KappaSplitReduction.lean): every level-`(m+1)` κ-path
to a goal admits a split point `mid` whose `projπ`-prefix is an `m`-goal AND whose
suffix carries `κ₂ ≥ 1`. This pass (i) delivers the **generic first-witness path
split** `WPath_first_witness_split` (fully unconditional: any `WPath` with a
decidable vertex predicate `P` true at the target splits at the FIRST `P`-vertex,
with firstness data `∀ x ∈ vs₁, P x → x = mid`); (ii) packages the level-`m`
precision predicate `projMPrecise` as a `DecidablePred`; (iii) proves the TRUE
arithmetic fact **`invStart_succ_not_mPrecise`** (the start is NOT `m`-precise, so
the first `m`-precision point is strictly *after* the start — the R1 trap can only
re-appear at the END, never the start); (iv) lifts the δ₊ per-edge laws to
`InvKappaPreciseEdge` monotonicity (τ=1/τ=3 zero RESET δ₊ to max; τ=2 zero UNCHANGED;
κ=−1 edge NON-DECREASING in δ₊); and, the headline, (v) the **valid reduction**
`blockBoundaryExists_of_firstMPrecisionSuffixPositive : FirstMPrecisionSuffixPositive
m Q → BlockBoundaryExists m Q`, which DISCHARGES the entire structural-split half and
isolates the **single remaining obligation** as the sharper, provably-non-circular
named Prop `FirstMPrecisionSuffixPositive` (on the first-`m`-precision suffix,
`κ₂ ≥ 1`). **Truth verdict: UNDETERMINED, leaning "the κ-route as conceived cannot
close it."** The pass also *refutes* the specific reduction line the task favoured
("mid = LAST `m`-precision point ⟹ suffix has no τ=1 zeros ⟹ κ₂ = n_one ≥ 1"): the
LAST `m`-precision point IS the goal (empty suffix, the R1 trap), and τ=1/τ=3 zeros
target NON-`m`-precise successors, so a "no `m`-precise interior" selector places no
constraint on them — the implication is a non-sequitur. The genuine open content is
the **one-edge discrete-log jump** (`oneEdge_rhoPlus_law`: ρ₊ can lift across the
whole final 22-digit gap in one edge), whose deciding configurations live at 3-adic
depth ≈ 3²¹ and are computationally invisible (real-graph probes top out at a
single-edge ν₃-jump of 10 < 22), so no counterexample is exhibitable and no proof is
reachable by enumeration.

**This is NOT a proof of Collatz, nor even of the full S202 alternative.** It is one
half (the slope-barrier half) of one branch of the S202 alternative, and it is
currently *uniform only for the toy index `m = 1`*. Reaching Collatz additionally
requires: (Level 1) the S202 alternative fully resolved **including** the
subcritical-access branch, and (Level 0) the **external "Bandujar reduction"**
connecting the S202 alternative to actual Collatz counterexamples. Neither is
formalized; the reduction is a non-formalizable mathematical claim *outside* this
program's current verified perimeter.

**Orthogonal new front (2026-05-30, S239).** A separate line attacks the OTHER
half of Collatz — **cycle exclusion** (no nontrivial cycles), independent of the
slope-barrier κ-route above. Built on the forward accelerated Syracuse map
`Syr n = (3n+1)/2^{ν₂(3n+1)}`, it proves — machine-checked, axiom-clean — the cycle
equation `2^A·a = 3^m·a + C` (explicit `C`), the strict corridor `3^m < 2^A`, and
the **period-1 and period-2 cases UNCONDITIONALLY** (`syr_no_nontrivial_fixedpoint`,
`syr_no_nontrivial_2cycle`). A companion module characterizes closed walks in the
inverse graph as an **order-of-2 / discrete-log** phenomenon (`2^W ≡ 1 mod 3^{R+j}`,
weight `≥ 2·3^{R+j−1}`), NOT forward cycles — refuting the naive closed-walk↔cycle
bridge. See §5.-3. This does **not** bring Collatz closer: `m ≥ 3` is finite-but-
tedious and unbounded period is blocked by **Baker's theorem** (linear forms in
logarithms, absent from Mathlib).

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
| **2-split** | **The `WPath`-split route to uniform-`m`**: `KappaPathSplit m Q` (prefix-κ ≥ `m`, suffix-κ ≥ `1`) + the `m=1` base ⟹ `defect ≥ m` for all `m`. Its residue is now packaged as the committed core `BlockBoundaryExists` (Level 2-BBE). | **OPEN** (crux re-packaged as 2-BBE) | `KappaPathSplit`, `uniform_slope_barrier_of_cert_and_split` (UniformBarrier.lean) |
| **2-split-R2** | R2 brick: the κ-preserving precision-reduction **functor** `projπ` lifts a level-`(m+1)` κ-path to a level-`m` κ-path (same κ), discharging R2's precision-tower step | **PROVEN** (new 05-30) | `InvKappaPreciseEdge_projectDown`, `WPath_projectDown`, `kappaProjectsDown_holds` (KappaSplitWork.lean) |
| **2-BBE** | `BlockBoundaryExists m Q` — the **single committed open core**: every `(m+1)`-κ-path to a goal splits at a `mid` with `projπ`-prefix an `m`-goal **and** suffix-κ ≥ 1. Proving it ∀`m` (+ committed `m=1` base + `uniform_slope_barrier_of_block`) ⟹ `defect ≥ m` ∀`m`. | **OPEN — UNDETERMINED** (truth verdict: leans "κ-route as conceived cannot close it") | `BlockBoundaryExists` (KappaSplitReduction.lean) |
| **2-BBE-split** | Structural-split half of 2-BBE: generic first-witness path split + the valid reduction `FirstMPrecisionSuffixPositive m Q → BlockBoundaryExists m Q`. **Discharges every conjunct of 2-BBE except `κ₂ ≥ 1`.** | **PROVEN** (new 05-30) | `WPath_first_witness_split`, `blockBoundaryExists_of_firstMPrecisionSuffixPositive`, `invStart_succ_not_mPrecise` (BlockBoundaryWork.lean) |
| **2-BBE-resid** | The lone residual of 2-BBE, isolated as a sharper named Prop: on the suffix from the FIRST `m`-precision vertex to the goal, `κ₂ ≥ 1`. Strictly weaker than 2-BBE (handed the firstness data; need not *exhibit* `mid`); provably non-circular. | **OPEN-NUMBER-THEORY** (the genuine crux: a 3-adic question at depth ≈ 3²¹) | `FirstMPrecisionSuffixPositive` (BlockBoundaryWork.lean) |
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

The 2026-05-30 passes added a **second, parallel route into Level 1a** — the
committed `WPath`-split core `KappaPathSplit` (**Level 2-split**), now re-packaged
as the single committed open Prop **`BlockBoundaryExists`** (**Level 2-BBE**) — and
discharged two sub-bricks as machine-checked theorems: the R2 precision functor
(**Level 2-split-R2**) and the entire **structural-split half** of `BlockBoundary‐
Exists` (**Level 2-BBE-split**: the generic first-witness split + the valid
reduction to `FirstMPrecisionSuffixPositive`). This does **not** move the honesty
line: the residual **Level 2-BBE-resid** (`FirstMPrecisionSuffixPositive` — on the
first-`m`-precision suffix, `κ₂ ≥ 1`) is still OPEN and is **UNDETERMINED** as to its
truth. The structural obstruction is now pinpointed exactly: the one-edge discrete-log
jump (`oneEdge_rhoPlus_law`) can in principle lift ρ₊ across the whole final 22-digit
gap in a single edge, making the first (= only) `m`-precision vertex coincide with
the goal (the uniform R1 trap, ⟹ FALSE); whether some intermediate `m`-precise vertex
with a `κ₂ ≥ 1` tail is instead forced (⟹ TRUE) is a question about the joint 3-adic
distribution of `ν₃(c−1)` and `ν₃(c−2^τ)` along reachable κ-paths, whose deciding
configurations sit at depth ≈ 3²¹ and are computationally invisible. The earlier
`mid`-non-constructibility witnesses (`IsGoal_projectDown_not_reflects`,
`kappa_no_canonical_depth_cut`) are subsumed: `WPath_first_witness_split` *does*
canonically select `mid` (the first witness), so the difficulty is no longer
"which `mid`" but the arithmetic `κ₂ ≥ 1` on its suffix.

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
   ▲ OPEN     (reachable via EITHER Level 2″ OR Level 2-split/2-BBE below)
   ├─────────────────────────────┐
Level 2-split / 2-BBE  KappaPathSplit m Q  ≡  BlockBoundaryExists m Q
   ┊ OPEN  ── crux now = κ₂≥1 on the first-m-precision suffix (NOT "which mid")
   ┊  R2 brick PROVEN (05-30): projπ precision functor lifts (m+1)-κ-path
   ┊          ↦ m-κ-path, same κ (InvKappaPreciseEdge_projectDown / WPath_projectDown);
   ┊  STRUCTURAL-SPLIT half PROVEN (05-30): WPath_first_witness_split canonically
   ┊          selects mid = FIRST m-precision vertex; invStart_succ_not_mPrecise ⇒
   ┊          trap only at END; reduction blockBoundaryExists_of_firstMPrecisionSuffix‐
   ┊          Positive discharges every conjunct EXCEPT κ₂≥1
   ┊  ▼
   ┊  Level 2-BBE-resid  FirstMPrecisionSuffixPositive m Q  (κ₂≥1 on that suffix)
   ┊     ✗?  UNDETERMINED ── the genuine crux; one-edge dlog jump
   ┊        (oneEdge_rhoPlus_law) can lift ρ₊ across the full 22-digit gap in ONE
   ┊        edge ⇒ first m-precision vertex = goal (R1 trap, FALSE) unless an
   ┊        intermediate m-precise vertex with κ₂≥1 tail is forced (TRUE); deciding
   ┊        configs at 3-adic depth ≈ 3²¹, computationally invisible (probes: ν₃-jump ≤ 10)
   ┊  Caveat C (inherited): InvStart wrong cylinder for m≥2 until migrated to aS202_at m
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
`WPath`-split `KappaPathSplit`, re-packaged as `BlockBoundaryExists` (Level 2-BBE,
§5.-2), whose R2 brick and **entire structural-split half** are now proven, leaving
the single residual `FirstMPrecisionSuffixPositive` (§5.-2). The two below are the
highest-leverage items *on the analytic route*; the split-route frontier (now the
arithmetic `κ₂ ≥ 1` residual, plus the `InvStart` migration) is ranked in §5.-2 and
the document summary.

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

### 5.-3 S239 new-vias study + cycle-exclusion line + closed-walk characterization — 2026-05-30 (verified, 0 sorry, axiom-clean)

After the κ-route reduced to the lone residual `FirstMPrecisionSuffixPositive`
(§5.-2, UNDETERMINED, depth ≈ 3²¹), this pass — at the user's request — **studied
new attack vectors** (4 grounded scouting agents) and **opened an orthogonal front**.

**Four-vias study verdicts.** ① **Cycle exclusion** (affine identity ⊗ closed walks)
— WINNER, most tractable new formal direction. ④ **Stress-test** the slope machinery
on `qn±r` variants — DONE: it correctly discriminates `3n+1` (descent, gm 0.755),
`3n−1` (detects the known cycle `{5,7}`), `5n+1` (divergent, gm 1.246); the
load-bearing signal is the REAL corridor drift `E[τ]=2 vs log₂q`, NOT the integer
defect (knife-edge ≈0, wrong sign on 5n+1) nor the raw forward κ-rate (regime-blind
≈0.5) — `tools/variant_probe.py`. ② **2-adic ⊗ 3-adic coupling** — the genuine deep
shot but years/unbounded; BinaryTensor's TBD superstructure (spectrum, ℓ², entropy)
is unformalized and there is NO existing 2↔3 link. ③ **Density/Tao** — dropped:
3–6 person-years, no Mathlib foundation, structural ceiling "almost all ≠ all".

**Two refuted scout "easy bricks" (rigor catches, in the project's refute-don't-patch
discipline).** (a) `cycle_rearrangement_iff_n_one`: the naive `n·(2^A−3^q)=B` holds
IFF `n=1` (the accumulator is root-normalized; nontrivial cycles need the GENERAL
equation, not `B`). (b) `tau n = ν₂(3n+1)` is FALSE — `tau` is the inverse-section
choice exponent (`2^tau·n ≡ 1 mod 3`), counterexample `n=10` (∈X): tau=2 but ν₂(31)=0.

**New module `CycleEquation.lean`** (commits 623baef, 3f260b9; forward Syracuse
framework, grounded in the real map `Syr n=(3n+1)/2^{ν₂(3n+1)}`):

| Lemma | Statement |
|---|---|
| `Syr`, `Syr_step` | `2^{ν₂(3a+1)}·Syr a = 3a+1` (exact step identity) |
| `partialA`, `cycleC`, `cycle_telescope` | telescoping closed form `2^{A_m}·a_m = 3^m·a_0 + C_m` |
| `cycle_equation`, `cycleC_pos`, `forward_cycle_corridor` | cycle eq (additive) + strict corridor `3^m < 2^{A_m}` |
| `syr_cycle_equation`, `syr_cycle_corridor` | the above anchored on any genuine `Syr` periodic point |
| **`syr_no_nontrivial_fixedpoint`** | **m=1 UNCONDITIONAL**: only positive `Syr` fixed point is 1 (`a∣3a+1 ⟹ a∣1`) |
| **`syr_no_nontrivial_2cycle`** | **m=2 UNCONDITIONAL**: `ab(2^{k₀+k₁}−9)=3(a+b)+1 ⟹ 2^A≥16 ⟹ 7ab≤3a+3b+1 ⟹ a=b=1` |
| `NoNontrivialSyrCycle` | the cycle conjecture; m=1,2 done; unbounded period behind **Baker** (not in Mathlib), marked never assumed |

**New module `ClosedWalk.lean`** (commit ceee0f1) — **refutes the naive
closed-walk↔forward-cycle bridge**, replaces it with the correct characterization:
the inverse graph is **layered by `j`** (`InvEdge_j_le`, `WPath_j_le`: `j` is
non-decreasing; one-edges keep `j`, zero-edges increment), so a **closed walk uses
only one-edges**, its residues telescope (`oneWalk_residue`) and — `v₀.c` being an
admissible unit — force **`2^W ≡ 1 (mod 3^{R+j})`** (`closed_oneWalk_two_pow_mod`):
an **order-of-2 / discrete-log** fact, NOT a forward cycle. Reusing the project's LTE
law `padicValNat_two_pow_sub_one`, any nontrivial closed walk has weight
**`W ≥ 2·3^{R+j−1}`** (`closed_oneWalk_weight_ge_order`) — the same astronomical slack
that obstructs the slope barrier, now on the closed-walk side.

**Honest bottom line.** Solid verified infrastructure on a NEW front (cycle exclusion)
plus several refuted shortcuts, but **Collatz is not materially closer**. The cycle
line is at its natural plateau: m=1,2 clean and unconditional; m≥3 finite-but-tedious
(Steiner-style); unbounded period blocked by Baker. All new lemmas: 0 sorry, axioms
`{propext, Classical.choice, Quot.sound}` (#print-audited). Forward cycle-exclusion
lives in `CycleEquation` (Syr framework), NOT in the inverse graph (the divergence/
barrier half). All builds used narrow module targets (never the root → no Q10 blow-up).

### 5.-2 BlockBoundaryExists attack pass — 2026-05-30 (verified, 0 sorry / 0 axiom, independently axiom-audited)

**This pass attacks the single committed open core `BlockBoundaryExists m Q`**
(KappaSplitReduction.lean, lines 72–80) — the re-packaged residue of `KappaPath‐
Split`. The committed target, matched verbatim by an explicit ascription on the
reduction lemma, is: every level-`(m+1)` κ-path from `InvStart (m+1)` to a goal with
`goal.j ≤ Q` splits as prefix `InvStart (m+1) ⟶ mid` ++ suffix `mid ⟶ goal` with
`κ = κ₁ + κ₂`, `vs = vs₁ ++ vs₂`, `projπ m mid` an `m`-goal, `mid.j ≤ Q`, and
`1 ≤ κ₂`. Proving it ∀`m` (+ the committed `m=1` base + `uniform_slope_barrier_of_block`)
⟹ the S202 slope barrier `defect ≥ m` for ALL `m`.

One new file, namespace `CollatzLean4.Admissible`, **0 sorry, 0 axiom**, built clean
against cached Mathlib (`lake build CollatzLean4.BlockBoundaryWork` → exit 0, well
clear of the `Cert_m1_Q10` blow-up; olean at
`.lake/build/lib/lean/CollatzLean4/BlockBoundaryWork.olean`; only the specific module
built; root aggregator untouched):

- `CollatzLean4/CollatzLean4/BlockBoundaryWork.lean` (imports `KappaSplitReduction`,
  `Nu3UnitInvariance`; hence the committed `projπ` functor, the ρ₊/δ₊ transition
  laws, and the analytic-barrier infrastructure transitively)

**The decomposition (honest, NOT the τ=1-zero line).** `BlockBoundaryExists` splits
into a fully-discharged **structural half** and a single isolated **arithmetic
residual**:

| Lemma | Statement | Role |
|---|---|---|
| **`WPath_first_witness_split`** (F1) | generic, fully unconditional: for any weighted edge predicate `E` and `DecidablePred P` with `P t`, `WPath E s t w vs` splits as prefix `s ⟶ mid` (interior `vs₁`) ++ suffix `mid ⟶ t` (interior `vs₂`) with `w=w₁+w₂`, `vs=vs₁++vs₂`, `P mid`, and the **firstness** witness `∀ x ∈ vs₁, P x → x = mid` (`mid` = FIRST `P`-target). Pure induction on `vs`. | **The carrier**: canonically selects the split point — "split at the first witness", not previously in the repo |
| `projMPrecise` + `instDecidableProjMPrecise` | `projMPrecise m v := IsGoal (projπ m v) (22m+2)` (⟺ `v.c ≡ 1 mod 3^(22m+2+v.j)` ⟺ δ₊(v) ≤ 22), as a `DecidablePred` | The level-`m` precision predicate F1 instantiates at |
| `projMPrecise_of_isGoal_succ` | `IsGoal v (22(m+1)+2) → projMPrecise m v` | The `P`-at-endpoint hypothesis F1 needs (repackages committed `IsGoal_projectDown`) |
| **`invStart_succ_not_mPrecise`** | TRUE arithmetic content: `1 ≤ m → ¬ projMPrecise m (InvStart (m+1))` (because `projπ m (InvStart (m+1)) = InvStart m` and `aS202 = 1+3^22 ≢ 1 mod 3^(22m+2)` since `22m+2 ≥ 24 > 22`) | The first `m`-precision point is strictly AFTER the start ⟹ the R1 trap (empty suffix ⟹ κ₂=0) can re-appear only at the END, never the start |
| **`FirstMPrecisionSuffixPositive`** | the sharper residual Prop (NAMED, not asserted): on the suffix from the FIRST `m`-precision vertex `mid` to the goal — handed the firstness data `∀ x ∈ vs₁, projMPrecise m x → x = mid` — `1 ≤ κ₂` | **The single remaining open obligation**; provably non-circular (firstness is strictly more data than the bare `(m+1)`-barrier) |
| **`blockBoundaryExists_of_firstMPrecisionSuffixPositive`** | **HEADLINE reduction**: `FirstMPrecisionSuffixPositive m Q → BlockBoundaryExists m Q`. F1 + `IsGoal_projectDown` + `WPath_kappa_j_monotone` discharge every conjunct of the target except `1 ≤ κ₂`, which is exactly the residual. Lands DEFINITIONALLY on the committed target (verified by explicit ascription). | **The structural-split half is fully DISCHARGED**; only the κ₂ arithmetic remains |
| `rhoPlus_le_cap`, `deltaPlus_le_cap` | `ρ₊(c,r) ≤ r`, `δ₊(c,r) ≤ r` | Cap bookkeeping for the δ₊ laws |
| `zeroEdge_tau1_deltaPlus_nondecr`, `zeroEdge_tau3_deltaPlus_nondecr` | τ=1/τ=3 zero-edge: `δ₊(v) ≤ δ₊(v')` (RESET to max) | δ₊ engine: odd-τ zeros raise the deficit |
| **`kappaEdge_kappaNeg1_deltaPlus_nondecr`** | the κ=−1 (only κ-lowering) edge is a τ=1 zero ⟹ `δ₊(v) ≤ δ₊(v')` | **The verified obstruction**: κ-spending edges DESTROY precision (lower κ₂ *and* raise δ₊) |
| `zeroEdge_tau2_deltaPlus_eq` | τ=2 zero-edge: `δ₊(v') = δ₊(v)` (UNCHANGED) | δ₊ drops are carried only by one-edges (or even-τ ≥ 4 zeros) |

**Truth verdict on `BlockBoundaryExists`: UNDETERMINED**, leaning toward "the κ-route
as currently conceived cannot close it." Two things are *settled negatively* and one
is genuinely open:

1. **The task-favoured line is refuted.** "mid = LAST `m`-precision point ⟹ suffix
   has no τ=1 zeros ⟹ κ₂ = n_one ≥ 1" fails twice over: (a) the `(m+1)`-goal *is* an
   `m`-goal (committed `IsGoal_projectDown`), so the LAST `m`-precision vertex is the
   goal itself — empty suffix, `κ₂ = 0`, the exact R1 trap; (b) even reading it as
   "first `m`-precision point", a "no `m`-precise interior" selector does NOT forbid
   τ=1/τ=3 zeros, because those edges target NON-`m`-precise successors
   (`c' ≡ 2 mod 3`; committed `oddZeroEdge_breaks_mPrecision`). So `κ₂ = n_one −
   n_τ1zero` is NOT pinned to `≥ 1` by any precision argument; the implication is a
   non-sequitur. The δ₊ laws here make this precise: a τ=1 zero both subtracts 1 from
   κ₂ and resets δ₊ to max, demanding *more* downstream one-edges, of unbounded
   discrete-log magnitude `ν₃(c − 2^τ)`.

2. **The genuine open content is the one-edge discrete-log jump.** By
   `oneEdge_rhoPlus_law` (ρ₊(c') = ν₃(c − 2^τ)) a single one-edge can lift ρ₊ across
   the entire final 22-digit gap, making the first (= only) `m`-precision vertex
   coincide with the goal — a *uniform* R1 trap ⟹ `BlockBoundaryExists` FALSE.
   Whether that single-edge final lift can ALWAYS be performed from a non-`m`-precise
   source, or whether some intermediate `m`-precise vertex with a `κ₂ ≥ 1` tail is
   forced (⟹ TRUE), is a question about the joint 3-adic distribution of `ν₃(c−1)` and
   `ν₃(c−2^τ)` along reachable κ-paths. The deciding configurations live at 3-adic
   depth ≈ 3²¹ (the discrete-log wall) and are **computationally invisible**:
   real-graph probes (m=1, 300k states) top out at a single-edge ρ₊ jump of ν₃ = 10
   < 22 — no counterexample exhibitable, no proof reachable by enumeration.

**Axiom footprint (independently re-audited via `#print axioms`).** Build confirmed
(exit 0, olean produced); 0 `sorry`, 0 custom `axiom` (all grep hits for
sorry/admit/axiom are in prose docstrings only). The two headline lemmas
(`WPath_first_witness_split`, `blockBoundaryExists_of_firstMPrecisionSuffixPositive`)
depend on **only** `{propext, Quot.sound}` — *cleaner* than the allowed set. The
remaining proof-carrying lemmas stay within `{propext, Classical.choice, Quot.sound}`
plus, on `invStart_succ_not_mPrecise` alone, the pre-existing permitted
`aS202_decomp._native.native_decide.ax_1_1` (the aS202 anchor, **not** introduced
here). No `sorryAx`, no new custom axiom. All 13 declarations typecheck against their
stated signatures; the reduction lands definitionally on the committed target in
KappaSplitReduction.lean.

**Net effect on the ladder.** A new core rung **Level 2-BBE** (`BlockBoundaryExists`,
OPEN/UNDETERMINED) is named; its **structural-split half** (**Level 2-BBE-split**) is
PROVEN; and its lone residual (**Level 2-BBE-resid** = `FirstMPrecisionSuffix‐
Positive`) is isolated as a sharper, provably-non-circular named Prop. The prior
`mid`-non-constructibility obstruction is **subsumed** — `WPath_first_witness_split`
canonically selects `mid`, so the crux migrates from "which `mid`" to the arithmetic
`κ₂ ≥ 1` on its suffix. Levels 2″/1a/1b/0 are **unchanged**. The route to Collatz is
**not materially advanced**: it is still gated behind the OPEN/UNDETERMINED residual
(now sharply localized), the subcritical-access branch, and the external Bandújar
reduction.

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
2. **Headline of the 2026-05-30 BlockBoundaryExists pass: the entire structural-split half of the single committed open core `BlockBoundaryExists m Q` is proven** — the generic first-witness path split `WPath_first_witness_split` canonically selects `mid` = the FIRST `m`-precision vertex, and the valid reduction `blockBoundaryExists_of_firstMPrecisionSuffixPositive : FirstMPrecisionSuffixPositive m Q → BlockBoundaryExists m Q` discharges **every conjunct of the committed target except `κ₂ ≥ 1`** (`BlockBoundaryWork.lean`, 0 sorry, 0 axiom, build-verified, no `Cert_m1_Q10`).
3. **The lone residual is now isolated as one sharper, provably-non-circular named Prop `FirstMPrecisionSuffixPositive`** (on the suffix from the first `m`-precision vertex to the goal, `κ₂ ≥ 1`). Supporting TRUE bricks: `invStart_succ_not_mPrecise` (the start is NOT `m`-precise ⟹ the R1 trap can re-appear only at the END) and the δ₊ per-edge monotonicity laws (`kappaEdge_kappaNeg1_deltaPlus_nondecr`: the only κ-lowering edge DESTROYS precision).
4. **Truth verdict: UNDETERMINED**, leaning "the κ-route as conceived cannot close it." The task-favoured "LAST `m`-precision point / no τ=1 zeros" line is **refuted** (the last `m`-precision point IS the goal ⟹ empty suffix; τ=1/τ=3 zeros target non-`m`-precise successors so the selector does not forbid them). The genuine crux is the **one-edge discrete-log jump** (`oneEdge_rhoPlus_law` can lift ρ₊ across the full 22-digit gap in one edge), whose deciding configs sit at 3-adic depth ≈ 3²¹ and are computationally invisible (probes: ν₃-jump ≤ 10 < 22) — so neither a counterexample nor a proof is reachable by enumeration.
5. **Ladder update:** new rungs **Level 2-BBE** (`BlockBoundaryExists`, OPEN/UNDETERMINED), **Level 2-BBE-split** (structural half, PROVEN 05-30), **Level 2-BBE-resid** (the residual, OPEN); the prior `mid`-non-constructibility obstruction is **subsumed** (the split now canonically picks `mid`, so the crux migrates from "which `mid`" to the arithmetic `κ₂ ≥ 1`). Axiom audit: the two headline lemmas on `{propext, Quot.sound}` only; rest within the allowed set + the pre-existing `aS202_decomp._native` anchor on one lemma; no `sorryAx`, no new custom axiom. (Earlier same day: Level 2-split-R2 functor PROVEN; prior 05-29: Level 2-bridge REFUTED, Level 4-truth added — LTE/dlog route stays dead.)
6. Levels 2″/1a (uniform-in-`m`), 1b (subcritical-access branch), 0 (Bandújar reduction) remain OPEN/EXTERNAL; the route to Collatz is **not materially advanced** — it is now gated behind a single sharply-localized arithmetic residual whose truth is itself undetermined, plus the unformalized subcritical branch and the external Bandújar reduction.
7. Single most valuable next step: **decide `FirstMPrecisionSuffixPositive`** — i.e. settle whether the one-edge discrete-log lift can always carry ρ₊ across the final 22-digit gap from a non-`m`-precise source (⟹ `BlockBoundaryExists` FALSE, killing the κ-route, a major honest finding) or whether an intermediate `m`-precise vertex with a `κ₂ ≥ 1` tail is forced (⟹ TRUE); this is a sharp 3-adic question about the joint distribution of `ν₃(c−1)` and `ν₃(c−2^τ)`, and is the gate before any further uniform-`m` progress (the `InvStart`→`aS202_at m` migration of Caveat C remains a clean prerequisite for `m ≥ 2`).
