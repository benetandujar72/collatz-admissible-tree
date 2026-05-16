"""
S233 feature-sweep: extend the collaborator's local ansatz with
candidate non-linear / 2D-modular features and test which (if any)
make the LP feasible on (m=1, Q=5), (m=2, Q=6) — the cases where the
plain ansatz failed.

Features tested:

  baseline     L(v) = 2*d+(v) - r-(v) + (j(v) - Q)
  + j2         + alpha * j(v)^2
  + j_dp       + alpha * j(v) * d+(v)
  + j_rm       + alpha * j(v) * r-(v)
  + dp2        + alpha * d+(v)^2
  + maxdp_rm   + alpha * max(d+(v), r-(v))
  + nu3_c      + alpha * nu3(v.c) capped       [the 3-adic valuation of c itself]
  + psi_2D_j   psi(c mod 3^h, j mod 3)         [doubles the index]
  + psi_2D_t   psi(c mod 3^h, c mod 9)         [refines by tau]

For each variant we sweep alpha in a small range and report feasibility.
"""

from __future__ import annotations
import sys
from collections import defaultdict
from typing import Dict, List, Tuple, Callable, Any

sys.path.insert(0, ".")
from s230_dual_search import S230Engine, kappa_precise
from s202_engine import State


def nu3(n: int, cap: int = 64) -> int:
    if n == 0:
        return cap
    v = 0
    while n % 3 == 0 and v < cap:
        n //= 3
        v += 1
    return v


def Lbase(v: State, Q: int, cap: int) -> int:
    return 2 * nu3(v.c - 1, cap) - nu3(v.c + 1, cap) + (v.j - Q)


def Lfeat_factory(extra: str, alpha: int) -> Callable[[State, int, int], int]:
    """Return L(v, Q, cap) for the chosen extra feature."""
    def L(v: State, Q: int, cap: int) -> int:
        base = Lbase(v, Q, cap)
        dp = nu3(v.c - 1, cap)
        rm = nu3(v.c + 1, cap)
        if extra == "baseline":   add = 0
        elif extra == "j2":       add = alpha * (v.j * v.j)
        elif extra == "j_dp":     add = alpha * (v.j * dp)
        elif extra == "j_rm":     add = alpha * (v.j * rm)
        elif extra == "dp2":      add = alpha * (dp * dp)
        elif extra == "maxdp_rm": add = alpha * max(dp, rm)
        elif extra == "nu3_c":    add = alpha * nu3(v.c, cap)
        elif extra == "psi_2D_j": add = 0  # handled via class index
        elif extra == "psi_2D_t": add = 0  # handled via class index
        else: raise ValueError(extra)
        return base + add
    return L


def class_index(v: State, h: int, extra: str) -> int:
    mod_h = 3 ** h
    base = v.c % mod_h
    if extra == "psi_2D_j":
        return base * 3 + (v.j % 3)
    if extra == "psi_2D_t":
        return base * 9 + (v.c % 9)
    return base


def num_classes(h: int, extra: str) -> int:
    if extra == "psi_2D_j": return 3 ** h * 3
    if extra == "psi_2D_t": return 3 ** h * 9
    return 3 ** h


def feasibility(m: int, Q: int, kappa_fn, h: int,
                extra: str, alpha: int,
                max_states: int = 200_000) -> Dict[str, Any]:
    eng = S230Engine(m=m, Q=Q, kappa_fn=kappa_fn)
    cert = eng.search(max_states=max_states)
    if cert["status"] != "barrier":
        return {"status": "search_" + cert["status"]}
    rows = cert["dist_table"]
    observed = {(r["j"], r["c"]) for r in rows}
    R = 22 * m + 2
    cap = R + Q
    Lfn = Lfeat_factory(extra, alpha)

    classes_involved = set()
    g_adj: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
    for r in rows:
        v = State(j=r["j"], c=r["c"])
        cv = class_index(v, h, extra)
        Lv = Lfn(v, Q, cap)
        for (vp, kappa_val) in eng.outgoing_edges(v):
            if (vp.j, vp.c) not in observed:
                continue
            cvp = class_index(vp, h, extra)
            Lvp = Lfn(vp, Q, cap)
            w = kappa_val - Lv + Lvp
            g_adj[cvp].append((cv, w))
            classes_involved.add(cv)
            classes_involved.add(cvp)
    if not classes_involved:
        return {"status": "no_constraints"}

    # virtual-source Bellman-Ford
    psi: Dict[int, int] = {k: 0 for k in classes_involved}
    V = len(classes_involved)
    relaxed = True
    rounds = 0
    while relaxed and rounds < V:
        relaxed = False
        rounds += 1
        for b, edges in g_adj.items():
            for (a, w) in edges:
                if psi[b] + w < psi[a]:
                    psi[a] = psi[b] + w
                    relaxed = True
    # negative-cycle check
    neg = False
    for b, edges in g_adj.items():
        for (a, w) in edges:
            if psi[b] + w < psi[a]:
                neg = True; break
        if neg: break
    if neg:
        return {"status": "infeasible"}

    # margin check at start vs reached goals
    v_start = State(j=0, c=eng.target)
    cs = class_index(v_start, h, extra)
    Ls = Lfn(v_start, Q, cap)
    shift = (m - Ls) - psi[cs]
    H_start = Ls + (psi[cs] + shift)
    H_goal_max = -10**9
    has_goal = False
    for r in rows:
        if r["c"] == 1:
            v = State(j=r["j"], c=1)
            cg = class_index(v, h, extra)
            if cg in psi:
                H_goal_max = max(H_goal_max, Lfn(v, Q, cap) + psi[cg] + shift)
                has_goal = True
    if not has_goal:
        H_goal_max = 0
    return {
        "status": "feasible",
        "margin": H_start - H_goal_max,
        "num_classes_used": len(classes_involved),
        "num_classes_total": num_classes(h, extra),
    }


def main():
    cases = [(1, 5), (2, 6)]
    variants = [
        ("baseline", [0]),
        ("j2",       [-3, -2, -1, 1, 2, 3]),
        ("j_dp",     [-2, -1, 1, 2]),
        ("j_rm",     [-2, -1, 1, 2]),
        ("dp2",      [-1, 1]),
        ("maxdp_rm", [-2, -1, 1, 2]),
        ("nu3_c",    [-2, -1, 1, 2]),
        ("psi_2D_j", [0]),
        ("psi_2D_t", [0]),
    ]
    h_test = 5
    print(f"\n=== Feature sweep at h={h_test}, kappa_precise. "
          f"OK = feasible with the indicated margin. ===\n")
    print(f"{'extra':<10} {'alpha':>5} | "
          + " | ".join(f"({m},{Q})" for (m, Q) in cases))
    print("-" * 50)
    for (extra, alphas) in variants:
        for alpha in alphas:
            row = f"{extra:<10} {alpha:>5}"
            for (m, Q) in cases:
                res = feasibility(m=m, Q=Q, kappa_fn=kappa_precise,
                                  h=h_test, extra=extra, alpha=alpha)
                if res["status"] == "feasible":
                    row += f" | OK m={res['margin']}"
                else:
                    row += f" | INF        "
            print(row)


if __name__ == "__main__":
    main()
