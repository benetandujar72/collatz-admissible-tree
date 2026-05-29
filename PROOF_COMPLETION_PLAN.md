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
Today's work added the **3-unit invariance lemma `nu3_unit_mul`** and the
**τ=2 "clean climb" law `zeroEdge_tau2_rhoPlus_climb`**, completing the verified
ρ₊ transition table on zero-edges `{τ=1 reset ✓, τ=2 climb ✓, τ=3 reset ✓}` and
unblocking the analytic (uniform-`m`) potential route.

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
| **4** | ρ₊ transition table on zero-edges: τ=1 reset, **τ=2 climb**, τ=3 reset; 3-unit invariance of ν₃; residue-congruence of ν₃ | **PROVEN** (today) | `nu3_unit_mul`, `nu3_congr_mod_pow`, `zeroEdge_tau2_rhoPlus_climb`, `zeroEdge_tau_1/3_deltaPlus_max` |
| **3** | κ-precise edge calculus: weight trichotomy, path decomposition `defect ≥ n_one − n_neg`, slice telescoping, j-monotonicity, exact-count predicate | **PROVEN** | `invEdge_weight_trichotomy`, `WPath_weight_decompose`, `InvPathCounts.*`, `WPath_kappa_*` |
| **2** | **Reduction**: an `AbsCert`/closure certificate (or finite-slice κ-potential) over `InvKappaPreciseEdge` ⟹ `S216BarrierForWords m Q m`. Non-circular (counts pinned via `InvPathCounts`). | **PROVEN** (the *implication*) | `S202_slope_barrier_from_kappa_cert`, `S216_barrier_for_words_via_kappa`, `S202_slope_barrier_from_kappa_precise_potential_bounded` |
| **2′** | The certificate's hypothesis **discharged unconditionally** for `m = 1`, `Q ∈ {1,3,5,8,10}` | **PROVEN** (`native_decide`) | `Cert_m1_Q{1,3,5,8,10}_kappa.barrier_*` |
| **2″** | The certificate's hypothesis discharged **uniformly in `m`** (one analytic Φ, not a per-`m` BFS table) | **OPEN-NUMBER-THEORY** | *target of §3 DAG* |
| **1a** | S202 slope-barrier branch: `defect ≥ m` for **all** `m` (uniform) | **OPEN-NUMBER-THEORY** | follows from 2″ via Level-2 reduction |
| **1b** | S202 alternative *fully* resolved (slope barrier **and** subcritical-access branch) | **OPEN-NUMBER-THEORY** | 1a + an unformalized second branch |
| **0** | Bandujar reduction: "S202 alternative ⟹ no Collatz counterexample", then Collatz | **EXTERNAL** (not formalized; not in repo as a proof) | — |

**Where the honesty line sits:** everything through **Level 2′** is genuinely
machine-checked. Level **2″ / 1a** is the first real mathematical gap (a uniform
3-adic argument). Levels **1b** and **0** are *additional* gaps, the last of which
is outside the formal program entirely.

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
   ▲ OPEN     (needs Level 2″)
Level 2″  uniform-in-m κ certificate / analytic Φ
   ┊ OPEN  ── analytic route now unblocked by Level-4 climb law
Level 2′  defect ≥ 1   (m=1, Q∈{1,3,5,8,10})           ✅ native_decide
   ▲ PROVEN
Level 2   κ-cert  ⟹  S216BarrierForWords m Q m          ✅ non-circular
   ▲ PROVEN
Level 3   κ-edge calculus + path decomposition           ✅
   ▲ PROVEN
Level 4   ρ₊ transition table + ν₃ unit/residue lemmas   ✅ (today)
```

---

## 3. Formalizable-lemma DAG (the part we can actually close in Lean now)

These are ordinary number-theory / dynamics lemmas that need no new external
input. They feed the **analytic uniform-`m` potential** (Level 2″), which is the
single most leveraged open target. Status reflects the current repo.

```
nu3_unit_mul ✅ ─────────────┐
                             ├──► oneEdge_rhoPlus_law (law 1, discrete-log)  [HARD, FORMALIZABLE-NOW]
nu3_congr_mod_pow ✅ ────────┤        │
                             │        ▼
nu3_mul_three ✅ ────────────┼──► zeroEdge_tau2_rhoPlus_climb ✅ (law 2, DONE today)
                             │
nu3_eq_padicValNat_of_lt ────┴──► lte_nu3_two_pow_sub_one ──► goal_forces_A_valuation_22
   [MEDIUM, not present]            [MEDIUM, not present]        [MEDIUM]
                                          │
                                          ▼
                                 one_edge_count_astronomical_lower_bound
                                          │
                                          ▼
                                 kappa_barrier_astronomically_slack ──► (feeds Level 2″ Φ / counting)
```

### 3.1 `nu3_unit_mul` — **PROVEN today** ✅

```lean
theorem nu3_unit_mul (u x c : Nat) (hu : u % 3 ≠ 0) : nu3 (u * x) c = nu3 x c
```
The critical-path unblocker: the capped 3-adic valuation is invariant under
multiplication by a 3-unit. Induction on the cap `c` mirroring the `nu3`
recursion; the load-bearing step is `(u*x)/3 = u*(x/3)` via `Nat.mul_div_assoc`
(needs `3 ∣ x`). File: `Nu3UnitInvariance.lean`. Axioms: `{propext, Quot.sound}`.

### 3.2 `nu3_congr_mod_pow` — **PROVEN today** ✅

```lean
theorem nu3_congr_mod_pow (c a b : Nat) (h : a % 3^c = b % 3^c)
    (ha : a ≠ 0) (hb : b ≠ 0) : nu3 a c = nu3 b c
```
The correct residue-transfer lemma. **Important correction to the original plan:**
the proposed `nu3_mod_pow : nu3 n c = nu3 (n % 3^c) c` is *false* at the
saturation residue `0` (e.g. `nu3 3 1 = 1` but `nu3 (3 % 3) 1 = nu3 0 1 = 0`,
because the `nu3 0 = 0` convention encodes "valuation 0", not "∞"). The
nonzero-hypothesis congruence form is the true and sufficient statement.

### 3.3 `zeroEdge_tau2_rhoPlus_climb` — **PROVEN today** ✅ (law 2)

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

### 3.4 `oneEdge_rhoPlus_law` (law 1, discrete-log) — **FORMALIZABLE-NOW, HARD, not present**

```lean
-- target (modular form; keep arguments in range via the residue representative)
theorem oneEdge_rhoPlus_law {R} (hR : 1 ≤ R) {v v' ω}
    (h_one : InvEdgeOne R v v' ω) :
    rhoPlus v'.c (R+v'.j) = nu3 ((v.c - 2^tau v'.c) % 3^(R+v'.j)) (R+v'.j)
```
Along a one-edge, `v'.c ≡ 2^{−τ}·v.c (mod 3^r)`, so `v'.c − 1 ≡ 2^{−τ}(v.c − 2^τ)`
and `2^{−τ}` is a 3-unit. Discharge with `nu3_unit_mul` (the unit) +
`nu3_congr_mod_pow` (the residue transfer, **now available**). HARD because it must
extract the inverse `2^{−τ}` from `invMod2Pow` and prove it coprime to 3, all
modulo `3^r`. *Both prerequisites it was waiting on (unit invariance + the
congruence form) now exist*, so this is the next concrete formalization target on
the analytic route. Not on the LTE critical path but required for any analytic
Bellman–Ford potential built from ρ₊.

### 3.5 `nu3_eq_padicValNat_of_lt` — **FORMALIZABLE-NOW, MEDIUM, not present**

```lean
theorem nu3_eq_padicValNat_of_lt (n c : Nat) (hn : n ≠ 0)
    (hlt : padicValNat 3 n < c) : nu3 n c = padicValNat 3 n
```
One-directional bridge from the custom capped `nu3` to Mathlib's `padicValNat` in
the cap-not-binding regime (`nu3 n c = min(padicValNat 3 n, c)`; this is the
unsaturated case; the saturated case is already `nu3_eq_cap_of_dvd`, S214Core:278).
Induction on `c` against `padicValNat.div` / `padicValNat.eq_zero_of_not_dvd`;
needs `Fact (Nat.Prime 3)`. **Leverage point:** once `nu3 = padicValNat` in the
astronomically-sub-`3^21` regime, *all* of Mathlib's lifting-the-exponent applies
for free. Optional for laws (1)/(2) (direct induction was simpler) but the gateway
for the LTE route below.

### 3.6 `lte_nu3_two_pow_sub_one` — **FORMALIZABLE-NOW, MEDIUM, not present**

```lean
theorem lte_nu3_two_pow_sub_one (S : Nat) (hS : S ≠ 0) :
    padicValNat 3 (2^S - 1) = padicValNat 3 S
```
The lifting-the-exponent core: `v₃(2^S − 1) = v₃(S)` (since `3 ∣ 2^2 − 1` and
`ord₃(2) = 2`). Mathlib has `multiplicity.Nat.pow_sub_pow` / the LTE API; this is a
specialization. Feeds the astronomical lower bound on one-edge counts.

### 3.7 `goal_forces_A_valuation_22` → `one_edge_count_astronomical_lower_bound` → `kappa_barrier_astronomically_slack` — **MEDIUM, not present**

The payoff chain: reaching the goal cylinder `[1]` from the start
`[aS202 = 1 + 3^22]` is a 3-adic discrete-log problem; LTE forces
`n_one ≳ 3^21`, so the κ-barrier `n_one − n_neg ≥ m` is astronomically slack for
the realizable range of `m`. These give a *quantitative* (and ideally uniform-`m`)
lower bound on `n_one`, which is exactly the Level-2″ input. **Caveat:** turning
"astronomically slack" into a uniform Lean theorem `defect ≥ m for all m` still
requires bounding `n_one` from below for *every admissible word*, not just showing
slack for a fixed `m` — this is where the genuine 3-adic dynamics enters and why
2″/1a is tagged OPEN, not FORMALIZABLE-NOW.

### Ranked next steps (highest leverage first)

1. **`oneEdge_rhoPlus_law` (law 1).** Unblocked today; completes the ρ₊ edge
   calculus (all four edge types), the prerequisite for *any* analytic ρ₊-based Φ.
2. **`nu3_eq_padicValNat_of_lt` (bridge).** Cheap, and opens the entire Mathlib LTE
   toolbox for the regime that matters.
3. **`lte_nu3_two_pow_sub_one`.** Mechanical given the bridge; the quantitative engine.
4. **`one_edge_count_astronomical_lower_bound`** then the uniform-`m` certificate
   (Level 2″) — the actual frontier.

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
  analytic certificate valid for all `m`. The §3 DAG is the plan to build one, but
  it is unfinished.

> If anyone summarizes this work as "proved Collatz", "proved the S202
> alternative", or "proved `defect ≥ m`", that is an **overclaim**. The defensible
> statement is: *"machine-checked, non-circular reduction of the S202 slope-barrier
> sub-route to a κ-weighted closure certificate, discharged unconditionally for
> `m = 1`, with the uniform-`m` analytic route now unblocked at the ρ₊ transition
> layer."*

---

## 5. What changed today (verified)

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

**Net effect on the ladder.** Level 4 is now complete on the zero-edge side, and
the two lemmas that *every* analytic-route lemma was blocked on (unit invariance +
residue congruence) now exist. This converts the one-edge discrete-log law
(§3.4, law 1) from "blocked" to "formalizable now". It does **not** change Levels
2″/1a/1b/0 — the uniform-`m` barrier, the subcritical branch, and the external
reduction remain open exactly as before.

---

### Document summary (6 lines)

1. This is the κ-precise **slope-barrier sub-route**, explicitly *not* a Collatz proof.
2. Ladder Levels 4→2′ are machine-checked; the κ-cert ⟹ `defect ≥ m` reduction is PROVEN and non-circular, but discharged unconditionally only for `m = 1`.
3. Levels 2″/1a (uniform-in-`m`), 1b (subcritical-access branch), 0 (Bandujar reduction) remain OPEN/EXTERNAL.
4. Today added `nu3_unit_mul` + `zeroEdge_tau2_rhoPlus_climb` (and `nu3_congr_mod_pow`), completing the zero-edge ρ₊ table and correcting the false `nu3_mod_pow` plan item.
5. The formalizable DAG (§3) now has its two blockers removed, opening the one-edge discrete-log law and the Mathlib-LTE bridge.
6. Single most valuable next formal step: **`oneEdge_rhoPlus_law` (law 1, §3.4)** — now unblocked, it completes the ρ₊ edge calculus for all four edge types and is the prerequisite for any uniform-`m` analytic potential (the real frontier).
