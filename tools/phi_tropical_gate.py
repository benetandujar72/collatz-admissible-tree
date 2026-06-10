"""
phi_tropical_gate.py — S240 numerical GATE for the tropical-nu3 potential class.

From the Iwasawa-limit scoping verdict: the strong (continuous-limit) form of route-B's
Phi is refuted, but the TROPICAL class survives un-refuted:

    Phi(j, c) = min_i ( alpha_i * min(nu3(c - 2^{s_i} * a_i), R+j) + beta_i * j + gamma_i )

with finitely many "Green terms" (targets a_i in {1, 4, aS202}, shifts 2^{s_i} along the
<2>-orbit).  GATE QUESTION: can ANY function of these tropical features express the exact
kappa-value tables of the verified m=1 certificates?

Method:
  1. Regenerate the exact min-kappa-from-start tables dist(j,c) with the same KappaEngine
     that produced the Lean certificates (Cert_m1_Q*_kappa), at the largest threshold T
     that still certifies (bigger T = bigger exact table).
  2. Features per state: j and w(a,s) = min(nu3((c - 2^s*a) mod 3^(R+j)), R+j)
     for a in {1, 4, aS202 mod 3^R}, s in 0..5.
  3. DETERMINISM TEST: if states with identical feature vectors carry different dist,
     NO function of the features (tropical or otherwise) can express the value table.
     Report collision rate = fraction of states in colliding buckets.
  4. If determinism ~holds: try small min-of-affine fits and report max error.

Honest scope: the table is min-kappa FROM the start (the certificate's psi); a barrier
Phi is a cost-TO-goal subsolution. Failure of the gate kills "tropical = exact value
function" and strongly disfavors (but does not formally refute) tropical subsolutions.
"""
from __future__ import annotations
import sys, time
from collections import defaultdict
from kappa_precise_probe import KappaEngine
from s202_engine import a202_mod

SHIFTS = [0, 1, 2, 3, 4, 5]


def v3_capped(x: int, M: int, cap: int) -> int:
    """nu3(x mod M), capped at cap (and = cap when x ≡ 0 mod M)."""
    x %= M
    if x == 0:
        return cap
    v = 0
    while x % 3 == 0 and v < cap:
        x //= 3
        v += 1
    return v


def best_table(m: int, Q: int, T_hi: int, max_states: int):
    """Largest-T certified table (exact dist on the relevant region)."""
    for T in range(T_hi, 0, -1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        res = eng.search_or_certify_bf(max_states=max_states)
        if res["status"] == "barrier_certificate":
            return T, eng, res["states"]
    return None, None, None


def gate(m: int, Q: int, T_hi: int = 5, max_states: int = 400_000):
    t0 = time.time()
    T, eng, states = best_table(m, Q, T_hi, max_states)
    if states is None:
        print(f"m={m} Q={Q}: no certified table up to T={T_hi} (witness or budget) — skip")
        return
    R = eng.R
    targets = [("one", 1), ("four", 4), ("astar", a202_mod(R))]
    # features
    rows = []
    for s in states:
        j, c, d = s["j"], s["c"], s["dist"]
        M = 3 ** (R + j)
        cap = R + j
        feats = [j]
        for (_, a) in targets:
            for sh in SHIFTS:
                feats.append(v3_capped(c - pow(2, sh, M) * a, M, cap))
        rows.append((tuple(feats), d, j, c))
    # determinism test
    buckets = defaultdict(list)
    for f, d, j, c in rows:
        buckets[f].append(d)
    n = len(rows)
    coll_buckets = {f: ds for f, ds in buckets.items() if len(set(ds)) > 1}
    n_coll = sum(len(ds) for ds in coll_buckets.values())
    max_spread = max((max(ds) - min(ds) for ds in coll_buckets.values()), default=0)
    print(f"=== m={m} Q={Q}  (R={R}, certified T={T}, states={n}, "
          f"buckets={len(buckets)}, {time.time()-t0:.1f}s) ===")
    print(f"  DETERMINISM: colliding buckets={len(coll_buckets)}  "
          f"states in collisions={n_coll} ({100.0*n_coll/n:.1f}%)  max dist-spread={max_spread}")
    # per-feature signal: mean dist by value of the nu3(c-1) feature (target one, shift 0)
    idx_one0 = 1  # feats[0]=j, then targets in order, 6 shifts each
    by_v = defaultdict(list)
    for f, d, j, c in rows:
        by_v[f[idx_one0]].append(d)
    sig = {v: (round(sum(ds) / len(ds), 2), len(ds)) for v, ds in sorted(by_v.items())}
    print(f"  signal nu3(c-1) -> (mean dist, n): {sig}")
    by_j = defaultdict(list)
    for f, d, j, c in rows:
        by_j[j].append(d)
    sigj = {v: (round(sum(ds) / len(ds), 2), len(ds)) for v, ds in sorted(by_j.items())}
    print(f"  signal j -> (mean dist, n): {sigj}")
    # verdict line
    if n_coll / n > 0.05:
        print(f"  GATE VERDICT: FAIL — dist is NOT a function of the tropical features "
              f"(collision {100.0*n_coll/n:.1f}% > 5%); the tropical class cannot express psi.")
    else:
        print(f"  GATE VERDICT: PASS determinism — attempting min-affine fit recommended.")
    return n_coll / n


if __name__ == "__main__":
    for Q in [3, 5]:
        gate(1, Q)
        print()
