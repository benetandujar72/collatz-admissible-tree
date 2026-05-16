#!/usr/bin/env python3
"""
S238 ψ-certificate verifier — PRECISE / sweep-aligned variant.

This is a companion to the S238 template verifier
(`s238_psi_verifier.py`) that uses the sharper conventions of the
sweep:

  * kappa_precise:  one-edge κ = +1
                    zero-edge κ = -1 if τ(α) = 1, else 0
                    (the template uses κ = -1 for every zero-edge)

  * rho_minus full-cap:  rho_minus(v) = nu3(v.c + 1, cap = R + j(v))
                         (the template caps at h)

  * arbitrary linear coefficients (a_dp, a_rm, a_j, a_jQ), read from
    the JSON `linear_coefficients` field. The template assumes the
    specific ansatz a_dp=0, a_rm=-1, a_j=0, a_jQ=1, which derived the
    closed-form local inequality
        ψ(z) − ψ(z') <= 1 + ρ-(v) − ρ-(v').
    For general coefficients we re-derive the per-edge inequality.

Usage:
    python s238_psi_verifier_precise.py psi_m1_Q3_h22_precise_corrected.json

Reports:
    - whether every observed edge (in the BF closure graph for (m, Q))
      satisfies H(v) <= κ(e) + H(v') under the supplied ψ table
      and linear coefficients;
    - whether H(start) - max_j H(goal_j) >= m, including ALL j in [0, Q]
      and not just goal vertices the BF closure happened to visit.

This is an *observed-graph* verifier. A full proof requires extending
the abstract over-cover (S234), which this script does NOT do.
"""

from __future__ import annotations
import sys, json, argparse
from pathlib import Path

sys.path.insert(0, ".")
from s230_dual_search import S230Engine, kappa_precise, kappa_coarse
from s202_engine import State


def nu3(n: int, cap: int = 10**18) -> int:
    if n == 0:
        return cap
    v = 0
    while n % 3 == 0 and v < cap:
        n //= 3
        v += 1
    return v


def H_at(v: State, Q: int, cap: int, coefs, psi, mod_h: int) -> int:
    a, b, c, d = coefs
    dp = nu3(v.c - 1, cap)
    rm = nu3(v.c + 1, cap)
    z = v.c % mod_h
    return (a * dp + b * rm + c * v.j + d * (v.j - Q)
            + int(psi.get(str(z), psi.get(z, 0))))


def verify(cert_path: Path) -> dict:
    cert = json.loads(cert_path.read_text())
    m = int(cert["m"])
    Q = int(cert["Q"])
    h = int(cert["h"])
    mode = cert.get("mode", "precise")
    psi = cert["psi"]
    coefs = cert.get("linear_coefficients", {})
    a = int(coefs.get("a_delta_plus", 0))
    b = int(coefs.get("a_rho_minus", -1))
    c = int(coefs.get("a_j", 0))
    d = int(coefs.get("a_jQ", 1))

    kfn = kappa_precise if mode == "precise" else kappa_coarse
    eng = S230Engine(m=m, Q=Q, kappa_fn=kfn)
    res = eng.search(max_states=200_000)
    if res["status"] != "barrier":
        return {"overall_ok": False,
                "reason": f"BF closure status={res['status']}"}
    rows = res["dist_table"]
    observed = {(r["j"], r["c"]) for r in rows}
    R = 22 * m + 2
    cap = R + Q
    mod_h = 3 ** h

    # 1. Edge inequalities  H(v) <= kappa + H(v').
    worst_violation = None
    n_edges = 0
    for r in rows:
        v = State(j=r["j"], c=r["c"])
        Hv = H_at(v, Q, cap, (a, b, c, d), psi, mod_h)
        for (vp, kappa_val) in eng.outgoing_edges(v):
            if (vp.j, vp.c) not in observed:
                continue
            Hvp = H_at(vp, Q, cap, (a, b, c, d), psi, mod_h)
            n_edges += 1
            gap = Hv - kappa_val - Hvp
            if gap > 0:
                if worst_violation is None or gap > worst_violation["gap"]:
                    worst_violation = {
                        "gap": gap,
                        "v": {"j": v.j, "c": v.c, "z": v.c % mod_h},
                        "v_prime": {"j": vp.j, "c": vp.c,
                                    "z": vp.c % mod_h},
                        "kappa": kappa_val,
                        "H_v": Hv, "H_vp": Hvp,
                    }

    # 2. Endpoint margin: H(start) >= m and H(goal_j) <= 0 for all j in [0, Q].
    start_v = State(j=0, c=eng.target)
    H_start = H_at(start_v, Q, cap, (a, b, c, d), psi, mod_h)
    H_goals = []
    for j in range(Q + 1):
        gv = State(j=j, c=1)
        H_goals.append((j, H_at(gv, Q, cap, (a, b, c, d), psi, mod_h)))
    max_goal = max(g for (_, g) in H_goals)

    return {
        "overall_ok": (worst_violation is None
                       and H_start >= m
                       and max_goal <= 0),
        "m": m, "Q": Q, "h": h, "mode": mode,
        "linear_coefficients": {"a_dp": a, "a_rm": b,
                                "a_j": c, "a_jQ": d},
        "n_observed_edges_checked": n_edges,
        "edge_check_pass": worst_violation is None,
        "worst_edge_violation": worst_violation,
        "H_start": H_start,
        "H_goal_per_j": H_goals,
        "max_H_goal": max_goal,
        "endpoint_margin": H_start - max_goal,
        "endpoint_required": m,
        "endpoint_pass": (H_start >= m and max_goal <= 0),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("psi_json", type=Path)
    args = parser.parse_args()
    result = verify(args.psi_json)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
