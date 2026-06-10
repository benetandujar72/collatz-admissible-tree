# ANGLE D1 — Two-case salvage of the uniform-in-m kappa barrier: VERDICT

Faithful scaled analog: cylinder index `M` plays `m+1`; gap `g` plays the real `22`.
Working level `B = g*M + 2` (goal: `c ≡ 1 mod 3^(B+j)`); coarse/IH ("m-precise") level
`R0 = g*(M-1) + 2 = B - g`; start residue `1 + 3^g` (mirrors `aS202 = 1 + 3^22`).
kappa: one-edge `+1`, tau=1 zero `-1`, tau>=2 zero `0`. Barrier target `kappa >= M`.

Metrics (exact finite reachable graph, SPFA/Bellman-Ford with negative edges):
- `K_all` = min total kappa, all paths InvStart->working-goal.
- `K_b`   = min total kappa over CASE-(b) paths (no m-precise INTERIOR vertex; m-precise = sinks).

## Findings (all reproduced; tools below)

**F1.** `K_b >= M` in every tested `(M,g,Q)`; min over all of `(K_b - M) = 0`. The case-(b)
bound `kappa >= m+1` is TRUE numerically, TIGHT at `g=2` (worst/adversarial gap). No violation.

**F2.** `K_all == K_b` for the floor in every case: the global min-kappa path is a case-(b)
path. Hence bounding case (b) below by `m+1` is EQUIVALENT to the full barrier — the two-case
split provides NO inductive reduction. (Some non-floor goals ARE strictly cheaper via case (a):
e.g. M=2,g=2,Q>=5 goal (5,1) has K_all=2 < K_b=8 — so case (a) is genuinely needed for coverage,
but never for the FLOOR.)

**F3.** The conjecture's case-(b) MECHANISM is FALSE. The entry class-7 vertex's discrete log
`W = dlog(s1) ~ 3^(22(m+1)+3)` is astronomical (m=1: 23 digits), so the FIXED-j one-edge ladder
from `dlog W` to `dlog 2` has `~W/3 ~ 10^23` one-edges. BUT the min case-(b) path does NOT take
that ladder: it uses zero-edges to RAISE j, and the deep-jump trap `c≡4` (work_dlog=2) sits at
SMALL work_dlog at HIGH j, reachable with only `~m` one-edges plus kappa<=0 zero-edges, total
`kappa ~ m+1`. So "no m-precise interior" does NOT force `kappa >= ladderlen`; N2 (deep-jump
uniqueness) is mod-9 only and pins NO kappa lower bound beyond the global barrier.

**F4.** `KappaPathSplit m Q  <=>  S202_kappa_precise_barrier_bounded (m+1) Q`. A path admits a
split (k1>=m, k2>=1) IFF its total `kappa >= m+1` — by discrete IVT: the prefix-kappa partial
sums step by {-1,0,+1} from 0 to K, so if `K>=m+1` the first index with `S_p=m` is interior
(`S_0=0<m`, `S_L=K>m`) and gives `k2=K-m>=1`. Verified on 170143 adversarial random walks, 0
failures. CONSEQUENCE: the `UniformBarrier.lean` induction step hypothesis is LOGICALLY
EQUIVALENT to its own conclusion; the step `barrier_step_of_split` is a tautology (the split is
automatic, needs no m-precision and no canonical cut, so `kappa_no_canonical_depth_cut` is not a
real obstruction). The "non-circularity witness" only shows the split carries per-piece data; the
EXISTENCE of the split is the barrier.

## Verdict
The two-case salvage does NOT salvage a uniform-in-m REDUCTION:
- case (a) (m-precise split + IH) is sound and needed for some goals, but covers only goals whose
  cheapest route already passes an m-precise vertex;
- case (b) is NOT directly forced `>= m+1` by N2 (mechanism refuted, F3); its bound is the
  residual barrier itself (F2);
- the whole `KappaPathSplit` induction is circular (F4).
The induction is INADEQUATE: there is no genuine `barrier(m) -> barrier(m+1)` content here.
Separately, the barrier `kappa >= m+1` is itself strongly corroborated (`K_b >= M` everywhere,
tight at the adversarial g=2) — it is TRUE but must be proved by a global/analytic argument
(Baker / Wall-A reachability of the dlog=2 trap), NOT by this per-block kappa induction.

## Tools (C:\Users\benet\Downloads\collatz-admissible-tree\tools\)
- `d1_decisive.py`   — K_all, K_b sweep (the headline table).
- `d1_falsify.py`    — falsification sweep hunting K_b < M (found NONE).
- `d1_dissect.py`    — traces the min case-(b) path (shows zero-edge navigation, refutes F3 mechanism).
- `d1_ka_vs_kb.py`   — per-goal case(a)-vs-(b): F2 (floor always case (b)).
- `d1_kappasplit_test.py` + inline IVT check — F4 (KappaPathSplit <=> barrier(m+1)).
Prior corroborating: `s241_min_kappa.py` (K* barrier metric), `b3_ladder_sim.py` (ladder lengths),
`b1_oneedge_avoid_precise.py` (case (b) nonempty).
