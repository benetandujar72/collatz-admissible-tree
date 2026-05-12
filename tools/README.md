# tools/ — S202 closure-certificate toolchain

External Python tooling for the S216/S217 program. The Lean side of
the project (in `CollatzLean4/`) defines the verification framework
(`InverseGraph.lean`, `PotentialBarrier.lean`); these Python tools
produce the **data** that Lean verifies.

## Files

- **`s202_engine.py`** — `S202Engine` class implementing the backward
  DFS over the inverse cylinder graph. Produces closure-style barrier
  certificates as Python dicts. Also includes `verify_w202()` for a
  sanity check of the published S202 word.

- **`cert_to_lean.py`** — exporter. Given `(m, Q)`, runs the engine and
  emits a self-contained Lean file that:
    - Hard-codes the dist table as `Cert_m{m}_Q{Q} : List (InvVertex × Int)`.
    - Defines `closure_check_m{m}_Q{Q} : Bool` and verifies it via
      `native_decide`.
    - Similarly for `no_goal_check_m{m}_Q{Q}`.

## Usage

```bash
# Sanity check + run a small experimental table
python3 s202_engine.py

# Generate a Lean certificate file (e.g., for m=1, Q=5)
python3 cert_to_lean.py 1 5 > ../CollatzLean4/CollatzLean4/Cert_m1_Q5.lean
# Then add to CollatzLean4.lean: import CollatzLean4.Cert_m1_Q5
```

## What the certificates prove

Each certificate emits `closure_holds_m{m}_Q{Q} : closure_check = true`,
which is the Bellman-Ford relaxation invariant for the dist table.
Combined with the no-goal check, this is **empirical evidence** that

> `𝒞^←_{S202}(m, Q) ≥ threshold`

(i.e., no admissible word `u` with `q(u) ≤ Q` and `n(u) ≡ aS202
(mod 3^(22m+2))` has defect `D(u) < threshold`).

**NOT yet provided**: the formal Lean theorem deducing this from the
two decidable checks. That implication (the closure-certificate-to-
barrier theorem, S212 path-word correspondence applied at depth) is
the next research step.

## Certificates currently lifted

| `m` | `Q` | `R` | states | Lean module |
|---|---|---|---|---|
| 1 | 3 | 24 | 22 | `CollatzLean4.Cert_m1_Q3` |

Further certificates can be added via `cert_to_lean.py`.
