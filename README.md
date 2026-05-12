# Collatz Admissible Tree — Lean 4 formalization

Formal Lean 4 verification of an admissible-inverse / 3-adic translation-set
framework around the Collatz conjecture, plus a 2-adic (Terras / TBD) parity
coordinate side, plus a constructive S202 cylinder access criterion.

**This project does NOT prove the Collatz conjecture.** It formalizes a
specific reformulation of the dynamics, certifies several structural
theorems (translation identity, resonance, defect bounds, the S202
counterexample to the auxiliary `A ≥ 2q` conjecture, the integrality
criterion for negative runs, the 3-adic lift of S206), and establishes
a CONDITIONAL criterion under which the asymptotic slope satisfies
`λ_asy < 2`.

## What's actually formalized

- **Inverse admissible branches** `Ψ₀, Ψ₁` on `n mod 9 ∈ X = {1,2,4,5,7,8}`
  with `τ`-table, accumulated parameters `(n, A, q, B)`, and the
  **translation identity** `3^q · n + B = 2^A` carried along every
  admissible word ([AdmissibleBasic.lean](CollatzLean4/CollatzLean4/AdmissibleBasic.lean)).
- **Automatic resonance** `B ≡ 2^A (mod 3^q)`, per-word and existential
  form (S192-A).
- **Word-to-translation-coverage equivalence** `coverage_translation_equiv`
  (S191-E).
- **`B_adm → B_free`**: every admissible `B` has the strictly-decreasing
  exponent representation `Σ 3^{i-1} · 2^{c_i}` (S192–S195 forward,
  [TranslationSets.lean](CollatzLean4/CollatzLean4/TranslationSets.lean)).
- **S202 counterexample** (`not_forall_admissible_triple_high_slope`):
  the rigid auxiliary `A ≥ 2q` is FALSE, witnessed by
  `(A, q, B) = (43, 22, 919447060349)`. The concrete word
  `wS202 = 10100000001000010000000000` from `initState` produces
  exactly this triple via `evalWord`
  ([Defect.lean](CollatzLean4/CollatzLean4/Defect.lean)).
- **S204-A slope bounds**: `3^q ≤ 2^A` and `q ≤ A` along every admissible
  run, plus `defect ≥ −q`.
- **S203-C/D negative-run framework**: `L^k(n) ∈ ℤ ⇔ n ≡ −1 (mod 3^k)`,
  and `3^k · L^k(n) = Lnum k n` under integrality
  ([NegativeRuns.lean](CollatzLean4/CollatzLean4/NegativeRuns.lean)).
- **S206 3-adic identity lifted** from `ZMod (3^24)` to every `ZMod (3^k)`
  via unit construction ([ThreeAdic.lean](CollatzLean4/CollatzLean4/ThreeAdic.lean)).
- **Computational reachability table**: explicit witnesses for
  `InImageTheta n` for `n ∈ {1, 4, 5, 11, 13, 16, 17, 40}`, plus the
  *empirical structural observation* that `n ∈ {2, 8}` are NOT reachable
  at any short depth ([Reachability.lean](CollatzLean4/CollatzLean4/Reachability.lean)).
- **2-adic / Terras coordinates** (Andújar TBD 2026): forward Collatz
  `T_lento`, `T_fast`, bit vector, parity vector, accumulated carry, the
  4-2-1 attractor cycle, Terras bijectivity at `k ≤ 3`
  ([BinaryTensor.lean](CollatzLean4/CollatzLean4/BinaryTensor.lean)).
- **S202 cylinder accessibility front**: `AccessibleToS202Cylinder m`,
  the structural decomposition `aS202 = 1 + 3^22` separating trivial
  (k ≤ 22) and non-trivial (k ≥ 23) regimes, and the `S202_alternative_conjecture`
  as a formal `Prop` ([S202Cylinders.lean](CollatzLean4/CollatzLean4/S202Cylinders.lean)).
- **S210/S211 constructive criterion**: word concatenation, defect
  additivity under iteration, and the conditional theorem
  `S211_S202_subcritical`: if `u` reaches the m-th cylinder with
  `D(u) < m` and the S209 cylinder-stability hypothesis holds for
  `wS202`, then `u ++ wS202^m` is an admissible word with `A < 2q`
  ([Concatenation.lean](CollatzLean4/CollatzLean4/Concatenation.lean)).

## Build

```bash
cd CollatzLean4
lake exe cache get          # pull precompiled Mathlib (recommended)
lake build                  # builds all 12 modules
```

Toolchain: `leanprover/lean4:v4.30.0-rc2`, Mathlib pinned in
`lake-manifest.json`. Current build: **8407 jobs, 0 `sorry`s, 0 axioms.**

## Module map

| Module | Content |
|---|---|
| [AdmissibleBasic](CollatzLean4/CollatzLean4/AdmissibleBasic.lean) | Definitions, translation identity, resonance |
| [TranslationSets](CollatzLean4/CollatzLean4/TranslationSets.lean) | `B_adm`, `B_free`, coverage equivalence |
| [Defect](CollatzLean4/CollatzLean4/Defect.lean) | Defect dynamics, S202 (n=251, A=43, q=22, D=−1), S204-A bounds |
| [NegativeRuns](CollatzLean4/CollatzLean4/NegativeRuns.lean) | `L^k` framework, S203-C/D |
| [PeriodicBlocks](CollatzLean4/CollatzLean4/PeriodicBlocks.lean) | S206 mod 3^24 identity |
| [ThreeAdic](CollatzLean4/CollatzLean4/ThreeAdic.lean) | S206 lifted to all `ZMod (3^k)` |
| [Reachability](CollatzLean4/CollatzLean4/Reachability.lean) | Computational `InImageTheta` table |
| [BinaryTensor](CollatzLean4/CollatzLean4/BinaryTensor.lean) | 2-adic coordinates, Terras, TBD |
| [S202Cylinders](CollatzLean4/CollatzLean4/S202Cylinders.lean) | S202 cylinder access, ladder `aS202 = 1 + 3^22`, alternative conjecture |
| [Concatenation](CollatzLean4/CollatzLean4/Concatenation.lean) | S210/S211 concatenation criterion |
| [CylinderStability](CollatzLean4/CollatzLean4/CylinderStability.lean) | S213: τ-trajectory stability, `runWord_cong` |
| [PotentialBarrier](CollatzLean4/CollatzLean4/PotentialBarrier.lean) | S214: abstract potential framework + `LocalPotentialCertificate` |

## Honest scope statement

What this codebase **does**:
- Reformulates Collatz into a 3-adic admissible-inverse framework, certified line-by-line.
- Refutes one rigid auxiliary conjecture (S202 high-slope) and reframes the asymptotic question.
- Provides a 2-adic coordinate scaffold complementary to the 3-adic engine.
- Closes the conditional S211 criterion: explicit subcritical-slope construction *given* the S209 cylinder-stability hypothesis.

What this codebase **does not** do:
- Prove the Collatz conjecture.
- Prove `λ_asy < 2` (the asymptotic slope bound) unconditionally.
- Close the S213 / S209 cylinder-stability hypothesis for `wS202`.
- Build the access-cost function `𝒞_{S202}(m)` explicitly.

The **strategic open front** is the `S202_alternative_conjecture` in
[S202Cylinders.lean](CollatzLean4/CollatzLean4/S202Cylinders.lean): either
the S202 3-adic fixed point is accessible from `1` with controlled
defect cost (subcritical slope follows), or there is a genuine 3-adic
accessibility barrier (structural obstruction discovered).

## Contributing

See [HANDOFF.md](HANDOFF.md) for the current research lines, including:
1. **S213**: cylinder stability lemma for `wS202` (discharges `h_uniform`).
2. **S211 search**: compute `𝒞_{S202}(m)` via backward DFS on cylinder predecessors.
3. **Bidirectional Terras for arbitrary k**: extend [BinaryTensor](CollatzLean4/CollatzLean4/BinaryTensor.lean).
4. **Per-word combinatorial defect formula**: cleaner accounting.

## License

MIT (see [LICENSE](LICENSE) when added by the author).
