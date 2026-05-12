# Collatz Admissible Tree — Lean 4 formalization

Formal verification of the admissible inverse Mori–Andújar tree (sessions S189–S207).
**This project does NOT prove the Collatz conjecture.** It formalizes a translation-set
reformulation and one resonant low-slope counterexample (S202) to an auxiliary conjecture.

## What's formalized

- Inverse branches `Ψ₀(n) = (2^τ(n)·n − 1)/3` and `Ψ₁(n) = 2^τ(n)·n`
  with `τ` on `n mod 9`.
- Accumulated parameters `(n, A, q, B)` with the **translation identity**
  `3^q · n + B = 2^A` carried along admissible words.
- Defect `D = A − 2q` and its exact dynamics per branch.
- **S202 counterexample** (theorem `not_forall_admissible_triple_high_slope`):
  the auxiliary conjecture `A ≥ 2q` for resonant admissible triples is FALSE,
  witnessed by `(A, q, B) = (43, 22, 919447060349)` with `A < 2q` and
  `B ≡ 2^A (mod 3^q)`.
- **S206 3-adic fixed-point identity** mod `3^24` verified by `native_decide`.
- Negative-run map `L(n) = (2n − 1)/3` framework and statement of the
  integrality criterion `L^k(n) ∈ ℤ ⇔ n ≡ −1 (mod 3^k)`.

## Build

```bash
cd CollatzLean4
lake exe cache get          # pull precompiled Mathlib (much faster)
lake build                  # builds all 5 modules
```

Toolchain: `leanprover/lean4:v4.30.0-rc2`, Mathlib pinned in `lake-manifest.json`.

## Status

5 modules compile. **4 `sorry`s remain**, all quarantined and documented in
[HANDOFF.md](HANDOFF.md) with proof plans and time estimates. None are used
as axioms; the proven theorems above stand independently.

## Contributing

Start with [HANDOFF.md](HANDOFF.md). The recommended first PR closes
`psiZero_integrality` + `step_zero_good` — these unblock the
unconditional form of `evalWord_translation_identity`.

For programmatic proof checking, see [AXLE_USAGE.md](AXLE_USAGE.md)
(uses the Axiom Lean Engine).

## License

MIT (see [LICENSE](LICENSE) when added by the author).
