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

5 modules compile. **0 `sorry`s remain.** Extensions beyond the initial
S189–S207 scope:
- `B_adm_resonance`: resonance `B ≡ 2^A (mod 3^q)` is automatic for every
  admissible triple (corollary of the translation identity).
- `B_adm_imp_B_free` (S192–S195, forward): every admissible `B` has the
  strictly-decreasing exponent representation
  `B = Σ_{i=1}^{q} 3^{i-1} · 2^{c_i}` with `A > c_1 > … > c_q ≥ 0`.

## Contributing

See [HANDOFF.md](HANDOFF.md) for the next research lines — `L^k` iteration
in `NegativeRuns`, computational accessibility tables, 3-adic limit
construction lifting `S206_fixed_point_mod` to `ℤ_3`, and defect/slope
bounds.

For programmatic proof checking, see [AXLE_USAGE.md](AXLE_USAGE.md)
(uses the Axiom Lean Engine).

## License

MIT (see [LICENSE](LICENSE) when added by the author).
