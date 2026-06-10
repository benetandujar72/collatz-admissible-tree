# Paper 1 (outline) — Machine-checked obstructions and closed-form barriers for the Collatz inverse tree

**Working title:** *Machine-checked obstructions for potential-based approaches to the
Collatz conjecture, with closed-form bounded barriers*

**Authors:** B. Andújar (formalization co-developed with Claude/Lean 4 + Mathlib)

**Thesis (one paragraph).** We formalize, in Lean 4 over a single verified graph model
(the admissible inverse cylinder tree of the accelerated Syracuse map), a complete
obstruction map for the natural proof strategies of the divergence half of Collatz,
together with the strongest closed-form positive results those obstructions permit.
The negative results are theorems, not heuristics: the per-block induction is provably
circular; no congruence invariant separates start from target at any finite modulus;
no 3-adically continuous potential — in any codomain — certifies the barrier; and the
optimal-path language is the period-1 filament, not a Sturmian word. The positive
results include a closed-form bit-length potential proving the bounded barrier without
search, and the full Eliahou–Hercher cycle pipeline. The residual difficulty is
isolated as a single named phenomenon (the archimedean Sturmian carry process of
rotation number log₂3), for which the solved function-field twin serves as a control
experiment.

---

## §1 Introduction
- The two halves of Collatz; the inverse-tree program; why machine-checked NEGATIVE
  results matter (cf. the 2026 unit-distance episode: the community redirects on
  rigorous obstruction knowledge).
- Contributions list (the six theorems below + the toolkit).
- Methodology: the numerical-gate → adversarial-verification → Lean funnel; all
  results 0 sorry; axiom audit per theorem (anchor inventory).

## §2 The verified model
- `InvVertex`, `InvEdgeOne`/`InvEdgeZero` (forced τ from the mod-9 table), κ-weights
  {+1, −1, 0}; `WPath`; the barrier statements (`S202_kappa_precise_barrier_bounded`).
- The mod-9 structure: `oneEdge_source_mod9_in_four_seven`, the deep-jump uniqueness
  (`oneEdge_deepjump_iff`: ν₃-jump ≥ 2 ⟺ target ≡ 1 mod 9, the dlog=2/c≡4 trap).

## §3 Obstruction I — the induction is circular
- `kappaPathSplit_iff_barrier_succ` (discrete IVT on {−1,0,+1} partial sums):
  the step hypothesis contains its conclusion.
- The canonical-first-split device: `not_firstMPrecisionSuffixPositive`,
  `not_blockBoundaryExists` — the ~10²¹-edge ladder exists by a closed-form argument
  (mod-6 shield, no enumeration).

## §4 Obstruction II — no finite-modulus invariant
- `invReachable_units`: every unit cylinder is reachable at every precision
  (the one-zero-edge-per-digit induction; `two_pow_tau_mul_mod9`: 2^{τ(α)}·α ≡ {4,7}
  mod 9 for every admissible class). Seals invariant-nonexistence as a theorem.

## §5 Obstruction III — no continuous potential, any codomain
- ℤ codomain: discrete ⟹ locally constant ⟹ finite modulus ⟹ dead (with §4).
- ℝ codomain: the ±1 attractor identities (`4(y−1)=3(c−1)`, `2(y+1)=3(c+1)`);
  `ν₃(aS202−1) = 22`; the attractor chain; `no_decaying_modulus_corrector`:
  every continuity modulus ω satisfies m ≤ ω(22+Q).
- The tropical/Green refutation witness (quotient-graph argument, 6 concrete edges).
- The Sturmian negative: optimal paths are the τ=1 filament (`min-κ(j) = −j`,
  the −1 attractor); the log₂3 slope is global, not local.

## §6 The positive frontier — closed-form barriers
- The master corridor `3^q·a₀ < 2^{A_q}·Syr^[q]a₀ ≤ 4^q·a₀` (one inequality, two
  shadows).
- `PhiBitlen` and `kappa_bounded_barrier_bitlen(_from)`: the bit criterion
  `4(m+Q)+1 ≤ size(start)`; faithful starts (`aS202_at`, kernel-decide certificates):
  m=2/Q≤16, m=3/Q≤23, anchor-free; the uniform `m+Q ≤ 8` corollary.
- The provable death of (bitlen, j)-linear potentials at Q ~ 22m: the wall, located.

## §7 The cycle half — the Eliahou–Hercher pipeline, formalized
- m = 1, 2, 3, 4 unconditional (elementary, Baker-free).
- Gap identity, frontier coupling (`SyrVerifiedUpTo` explicit), mediant exclusion
  (`mediant_period_bound`, pure ℕ unimodular identity), `fastPowAux` kernel
  certificates; instances 359 and 16 266; the literature-shaped bridge
  (`syrVerified_of_collatzVerified`).

## §8 The difficulty, named — and the function-field control
- The four walls are one object: effective rational approximation of log₂3 =
  the archimedean Sturmian carry process.
- The 𝔽₂[x] twin (HMYZ 2008; Behajaina–Paran 2023/25; Monks 2025 conjugation):
  a theorem because degree is carry-free; its naive Baker is FALSE (Frobenius unit
  gaps) yet the theorem stands ⟹ the integer difficulty is not "missing Baker".
- The CMS question (carry Mason–Stothers), weak and orbit forms; Stewart 1980 as
  the only effective anchor; Stérin–Woods (Collatz embeds base conversion).

## §9 Related work and methodology notes
- Tao 2019 (the exact Syracuse identity is formalized in the corpus); Simons–de
  Weger, Hercher; the orbit-decidability taxonomy (Z[1/6]⋊Z², the named open strip);
  Conway/Kurtz–Simon undecidability of generalizations.
- The agentic-formalization workflow; axiom hygiene (9 anchors removed); gates
  reproducibility (tools/ committed).

## §10 Open problems
- CMS (both forms); the hybrid potential corner; the word-level faithful migration;
  the cycle ceiling beyond mediant pairs (pow-by-squaring certificates make pairs
  mechanical; the ceiling is mathematics, not engineering).

**Appendix A.** Axiom audit table per theorem.
**Appendix B.** The Lean module map (≈35 modules) and build instructions.
**Appendix C.** Numerical gates: methodology and data (committed under tools/).

---

*Estimated length: 25–30 pp. Target: arXiv math.NT + math.LO cross-list; the Lean
artifact tagged at the corresponding commit.*
