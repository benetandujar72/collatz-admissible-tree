# Handoff — Collatz Admissible Tree (S189–S207)

**Branch:** `main` (commit `824cf54`)
**Toolchain:** `leanprover/lean4:v4.30.0-rc2`, Mathlib pinned in `lake-manifest.json`
**Build:** `cd CollatzLean4 && lake exe cache get && lake build`

All five new modules compile. **2 `sorry`s remain** (down from 4 in initial
commit `e72c8d0`):
  - `step_zero_preserves_X` (AdmissibleBasic) — 18-case mod-27 analysis
  - `coverage_translation_equiv` (TranslationSets) — unblocked, ~30 min

Both `step_zero_good` and `psiZero_integrality` are now proven, so
`evalWord_translation_identity` (S189–S191) is unconditional modulo
`step_zero_preserves_X` (which only enters via the joint `Inv` invariant).

`negative_run_integrality_iff` (S203-C) is also fully proven.

## What's proven (no `sorry`)

| Theorem | File | Tactic |
|---|---|---|
| `step_one_good` | AdmissibleBasic | `ring` + `pow_add` |
| `tau_mod` | AdmissibleBasic | `Nat.mod_mod` |
| `step_one_preserves_X` | AdmissibleBasic | `rcases` on `InX` + `decide` per case |
| `init_good`, `init_inv` | AdmissibleBasic | `simp` / `decide` |
| `defect_step_one`, `defect_step_zero` | Defect | `simp` + `ring` |
| `S202_translation_identity` | Defect | `native_decide` |
| `S202_resonance` | Defect | `native_decide` |
| `S202_low_slope` | Defect | `native_decide` |
| `S202_abstract_defect_negative` | Defect | `native_decide` |
| **`not_forall_admissible_triple_high_slope`** | Defect | `omega` from above |
| `S202_q`, `S202_n_actual`, `S202_A_actual`, `S202_B_actual`, `S202_defect_actual` | Defect | `native_decide` |
| `S206_fixed_point_mod` (3-adic `(2^43 − 3^22)·a ≡ B mod 3^24`) | PeriodicBlocks | `native_decide` |
| `S206_a_mod9`, `S206_repeat_from_251_q`, `S206_repeat_from_251_A`, `S206_not_direct_repeat_low_slope` | PeriodicBlocks | `native_decide` |

## Open `sorry`s (priority order for collaborators)

### 1. `step_zero_good` (`AdmissibleBasic.lean:93`)

**Statement.** Under `InX s.n` and `GoodState s`, the "zero" branch preserves the translation identity.

**Math.** Given `3 ∣ 2^τ(n)·n − 1` (integrality, see below), then
```
3^(q+1) · ((2^τ·n − 1) / 3) + (2^τ·B + 3^q)
  = 3^q · (2^τ·n − 1) + 2^τ·B + 3^q
  = 2^τ · (3^q·n + B)
  = 2^τ · 2^A           (using h)
  = 2^(A+τ).
```

**Plan.**
1. First prove auxiliary `psiZero_integrality (h : InX n) : 3 ∣ (2^tau n * n − 1)`.
   - 6-case `rcases` on `InX n`; write `n = 9·(n/9) + n%9` via `Nat.div_add_mod`; for each residue τ is fixed; `omega` or `decide` after expansion. Watch out for `Nat`'s truncated subtraction — may need `Nat.sub_one_dvd_iff` or to lift to `Int`.
2. Then close `step_zero_good` by `Nat.div_mul_cancel` on the integrality witness and `ring` for the algebra.

**Time estimate.** 1–2 hours for someone fluent in Mathlib's `Nat`/`Int` divisibility.

### 2. `step_zero_preserves_X` (`AdmissibleBasic.lean:122`)

**Statement.** Under `InX s.n`, the "zero" branch keeps the new `n` inside `X`.

**Math.** `n' = (2^τ(n)·n − 1)/3`. The value of `n' mod 9` depends on `n mod 27` (not just `n mod 9`), so the analysis has 18 cases (6 residues mod 9 × 3 lifts mod 27). All 18 land in `X` (verified by hand — table in commit message of this file).

**Plan.**
1. Use `Nat.div_add_mod n 27` and `interval_cases (n % 27)`.
2. For each of the 18 valid residues `r ∈ {1,2,4,5,7,8} × {0,9,18}`, evaluate `(2^τ(r)·r − 1)/3 mod 9` and check membership in `X`.
3. The other 9 residues are excluded by `hX` plus `Nat.mod_mod_of_dvd n (9 ∣ 27)`.

**Time estimate.** 2–4 hours; can probably automate with a custom tactic or `decide` after a generic rewriting lemma.

### 3. `coverage_translation_equiv` (`TranslationSets.lean:38`)

**Statement.** `(∀ n ∈ X, ∃ w, evalWord w .n = n) ↔ (∀ n ∈ X, ∃ A q B, B_adm A q B ∧ 3^q·n + B = 2^A)`.

**Math.** Direct from the translation identity (`evalWord_translation_identity`) and the definition of `B_adm`. Only delicate point: the reverse direction needs cancellation by `3^q` to extract `n = (evalWord w).n` from the identity (use `Nat.add_left_cancel` + positivity of `3^q`).

**Plan.** Two-way `constructor`; both directions are short once `evalWord_translation_identity` is fully closed (so depends on #1 above).

**Time estimate.** 30–60 minutes after #1.

### 4. `negative_run_integrality_iff` (`NegativeRuns.lean:19`)

**Statement.** `(3^k : Int) ∣ (2^k·n + 2^k − 3^k) ↔ n ≡ −1 (mod 3^k)`.

**Math.** Since `gcd(2^k, 3^k) = 1`, `2^k` is invertible mod `3^k`. Then
```
2^k·n + 2^k − 3^k ≡ 2^k·(n + 1) (mod 3^k),
```
which is `0 mod 3^k` iff `n + 1 ≡ 0 mod 3^k` iff `n ≡ −1 mod 3^k`.

**Plan.** Use `Int.ModEq`, `Nat.Coprime.pow_right`, and `Int.ModEq.cancel_left_of_coprime`.

**Time estimate.** 30–45 minutes.

## How collaborators should run AXLE

AXLE is a remote service; install locally and the CLI POSTs files to its API:

```bash
pip install axiom-axle
axle check --environment lean-4.29.0 --mathlib-options --ignore-imports \
  - < CollatzLean4/CollatzLean4/AdmissibleBasic.lean
```

For per-file local builds, prefer `lake env lean <file>` since AXLE's environment is fixed at `import Mathlib` and pinned to v4.29.0 (this project is on v4.30.0-rc2; cross-file imports won't resolve via AXLE).

## Conventions

- `Branch.zero ↔ Ψ₀(n) = (2^τ(n)·n − 1)/3` (the "hard" inverse, increments `q`).
- `Branch.one  ↔ Ψ₁(n) = 2^τ(n)·n` (the "easy" inverse, leaves `q` fixed).
- `τ` table on `n mod 9`: `{1↦2, 2↦1, 4↦2, 5↦3, 7↦4, 8↦1}`, else `0` (sentinel for `n ∉ X`).
- All admissible runs start at `initState = ⟨n=1, A=0, q=0, B=0⟩`.

## Known convention mismatch (S202)

The S202 published constants `(n=251, A=43, B=919447060349, defect=−1)` do NOT come from `evalWord wS202` under the formal `step` semantics (which gives `(n=1035769, A=55, B=3525268288809647, defect=11)`). Only `q=22` agrees. The published constants ARE a valid resonant admissible triple — this is what the abstract `not_forall_admissible_triple_high_slope` theorem captures. The exact word that produces `(43, 22, 919447060349)` from `initState` under our `step` (if any exists at all) is an open question; see `memory/s202_convention_mismatch.md` for diagnostics.

## Open mathematical problems (NOT to be added as `axiom`)

- Accessibility from `1` to cylinders of the S202 fixed point.
- Asymptotic slope `λ_asy < 2`.
- Full coverage `∀ n ∈ X, ∃ w, (evalWord w).n = n` (this is equivalent to the Collatz core inside this model — DO NOT close).
- Distribution of `R_adm(A, q)`.

## Suggested first PR for a new collaborator

Close `psiZero_integrality` + `step_zero_good` (#1 above). That's the keystone: it removes 2 of the 3 `sorry`s in `AdmissibleBasic.lean` and unblocks `coverage_translation_equiv` (#3).
