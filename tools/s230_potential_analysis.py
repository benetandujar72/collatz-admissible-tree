"""
S230 dual-potential analysis.

Given a closed BF certificate for the combinatorial cost
kappa(e) = +1 if one, -1 if zero (or zero-with-tau=1 in the precise
variant), define

    H(v) := T - dist[v]

where dist[v] is the minimal kappa-cost from start to v. Then H is a
valid dual potential: H(v) <= H(v') + kappa(e) along every edge, with
H(start) = T = m and H(g) <= 0 for every reached goal.

This script extracts H from the certificate JSON and asks the
Tao-style question: is H a closed-form function of the 3-adic
coordinates (delta+, rho-, j, c mod 3^h)?

We answer empirically by:

  - tabulating H against (delta+, rho-, j, c mod 3^h) for h=4..8;
  - reporting the slope of a linear least-squares fit H ~ a*delta+ +
    b*rho- + c*j + intercept;
  - reporting the residual after the linear fit and its dependence on
    (c mod 3^h) for h=4..8.

If H is well-fit by a linear function in (delta+, rho-, j) the dual
potential is essentially "S214-style" and easy to formalise. If a
significant residual depends on (c mod 3^h), that residual is the
psi term that S214 conjectures.
"""

from __future__ import annotations
import sys
from collections import defaultdict
from typing import Dict, List, Any

# Reuse the engine.
sys.path.insert(0, ".")
from s230_dual_search import S230Engine, kappa_precise, kappa_coarse


def nu3(n: int) -> int:
    """3-adic valuation, capped at 64 (we never need more here)."""
    if n == 0:
        return 64
    v = 0
    while n % 3 == 0 and v < 64:
        n //= 3
        v += 1
    return v


def delta_plus(c: int, mod_log: int) -> int:
    """nu_3(c - 1) capped at mod_log."""
    return min(nu3(c - 1), mod_log)


def rho_minus(c: int, mod_log: int) -> int:
    """nu_3(c + 1) capped at mod_log."""
    return min(nu3(c + 1), mod_log)


def linfit(X: List[List[float]], y: List[float]):
    """Naive least-squares: solve X^T X beta = X^T y via the normal
    equations. Tiny n so this is fine; no numpy dependency."""
    n = len(y)
    k = len(X[0])
    XtX = [[0.0] * k for _ in range(k)]
    Xty = [0.0] * k
    for i in range(n):
        for a in range(k):
            Xty[a] += X[i][a] * y[i]
            for b in range(k):
                XtX[a][b] += X[i][a] * X[i][b]
    # Gauss-Jordan elimination.
    A = [row[:] + [Xty[i]] for i, row in enumerate(XtX)]
    for p in range(k):
        # pivot
        pivot = max(range(p, k), key=lambda r: abs(A[r][p]))
        A[p], A[pivot] = A[pivot], A[p]
        if abs(A[p][p]) < 1e-12:
            return None
        for r in range(k):
            if r != p:
                factor = A[r][p] / A[p][p]
                for c_ in range(p, k + 1):
                    A[r][c_] -= factor * A[p][c_]
    beta = [A[r][k] / A[r][r] for r in range(k)]
    # R^2
    mean_y = sum(y) / n
    ss_tot = sum((yi - mean_y) ** 2 for yi in y)
    ss_res = 0.0
    for i in range(n):
        pred = sum(X[i][a] * beta[a] for a in range(k))
        ss_res += (y[i] - pred) ** 2
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0
    return beta, r2, ss_res, n


def analyse(m: int, Q: int, kappa_fn, label: str,
            max_states: int = 5_000_000) -> Dict[str, Any]:
    print(f"\n=== Analysis: m={m}, Q={Q}, kappa={label} ===")
    eng = S230Engine(m=m, Q=Q, kappa_fn=kappa_fn)
    cert = eng.search(max_states=max_states)
    if cert["status"] != "barrier":
        print(f"  status={cert['status']}; skipping analysis.")
        return {"status": cert["status"]}
    T = cert["T"]
    rows = cert["dist_table"]
    print(f"  closed in {cert['states_seen']:,} states "
          f"({cert['elapsed_s']:.2f}s); T = {T}.")
    print(f"  H(start) = T - dist[start] = {T} - 0 = {T}.")

    # Build feature matrix.
    R = 22 * m + 2
    mod_log_cap = R + Q  # the moduli used in the graph
    X, y = [], []
    rows_aug = []
    for row in rows:
        j, c, d = row["j"], row["c"], row["dist"]
        H = T - d
        d_plus = delta_plus(c, mod_log_cap)
        r_minus = rho_minus(c, mod_log_cap)
        X.append([1.0, float(d_plus), float(r_minus), float(j)])
        y.append(float(H))
        rows_aug.append((j, c, d, H, d_plus, r_minus))

    # Linear fit  H ~ a0 + a1*delta+ + a2*rho- + a3*j.
    res = linfit(X, y)
    if res is None:
        print("  linear fit singular.")
        return {"status": "fit_singular"}
    beta, r2, ss_res, n = res
    print(f"  linear fit H ~ {beta[0]:+.3f} "
          f"{beta[1]:+.3f} d+  {beta[2]:+.3f} r-  {beta[3]:+.3f} j")
    print(f"  R^2 = {r2:.4f}  (n = {n}, residual ss = {ss_res:.2f})")

    # Residual histogram bucketed by c mod 3^h for h = 4, 5, 6, 7.
    print("  Residual concentration by c mod 3^h:")
    for h in (4, 5, 6, 7):
        mod = 3 ** h
        buckets: Dict[int, List[float]] = defaultdict(list)
        for (j, c, d, H, dp, rm) in rows_aug:
            pred = beta[0] + beta[1] * dp + beta[2] * rm + beta[3] * j
            buckets[c % mod].append(H - pred)
        # Within-bucket variance vs total variance.
        within = 0.0
        ngroup = 0
        for _, vals in buckets.items():
            if len(vals) > 0:
                mu = sum(vals) / len(vals)
                within += sum((v - mu) ** 2 for v in vals)
                ngroup += 1
        total = sum(((H - (beta[0] + beta[1] * dp + beta[2] * rm + beta[3] * j))) ** 2
                    for (j, c, d, H, dp, rm) in rows_aug)
        between_share = 1.0 - within / total if total > 0 else 0.0
        print(f"    h={h}, mod=3^{h}={mod}: {ngroup} buckets, "
              f"between-bucket share of residual variance = "
              f"{between_share*100:.1f}%")

    return {
        "status": "barrier",
        "m": m, "Q": Q, "kappa": label,
        "T": T,
        "fit_coeffs": {
            "intercept": beta[0],
            "delta_plus": beta[1],
            "rho_minus": beta[2],
            "j": beta[3],
            "R2": r2,
        },
    }


if __name__ == "__main__":
    cases = [
        (1, 3, kappa_precise, "precise"),
        (1, 5, kappa_precise, "precise"),
        (1, 8, kappa_precise, "precise"),
        (2, 6, kappa_precise, "precise"),
        (3, 6, kappa_precise, "precise"),
        (1, 3, kappa_coarse,  "coarse"),
        (1, 5, kappa_coarse,  "coarse"),
        (2, 6, kappa_coarse,  "coarse"),
    ]
    out = []
    for (m, Q, kfn, lbl) in cases:
        try:
            r = analyse(m, Q, kfn, lbl)
        except Exception as e:
            print(f"  ERROR: {e}")
            r = {"status": "error", "error": str(e)}
        out.append({"m": m, "Q": Q, "kappa": lbl, "result": r})

    print("\n=== Cross-case coefficient table ===")
    print(f"{'m':>3} {'Q':>3} {'kappa':<8} "
          f"{'a_dplus':>10} {'a_rminus':>10} {'a_j':>8} {'R^2':>7}")
    for entry in out:
        r = entry["result"]
        if r.get("status") == "barrier":
            c = r["fit_coeffs"]
            print(f"{entry['m']:>3} {entry['Q']:>3} {entry['kappa']:<8} "
                  f"{c['delta_plus']:>10.3f} {c['rho_minus']:>10.3f} "
                  f"{c['j']:>8.3f} {c['R2']:>7.4f}")
