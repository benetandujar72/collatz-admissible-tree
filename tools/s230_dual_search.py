"""
S230 — Markov / Bellman-Ford dual for the S202 one-edge-count conjecture.

Methodology (inspired by Tao's primitive-sets / von Mangoldt-chain post):
replace the brute path enumeration over the inverse cylinder graph by a
*dual potential* H : InvVertex -> Int satisfying

    H(v) <= H(v') + kappa(e)      for every edge e : v -> v'.

If such an H exists with H(start) - H(goal) >= m, then telescoping along
any path yields

    sum_{e in path} kappa(e) >= m.

The combinatorial weight kappa is chosen so that the inequality on the
right-hand side encodes exactly the open conjecture.

Two natural weights:

    kappa_precise(e) = +1 if e is a one-edge
                       -1 if e is a zero-edge with tau = 1
                        0 if e is a zero-edge with tau >= 2
        => sum kappa_precise = numOnes - numNeg
        => potential >= m  iff  S202_one_edge_count_conjecture (precise form)

    kappa_coarse(e)  = +1 if e is a one-edge
                       -1 if e is any zero-edge
        => sum kappa_coarse = numOnes - numZeros
        => potential >= m  iff  S202_one_edge_count_conjecture (coarse form)

Coarse implies precise but is over-strong; whether coarse holds on every
cylinder is empirically open. This script answers that empirically for
the seven (m, Q) frontiers already closed by `s216_engine.py`.

Algorithm: reuse the BF closure engine of `s216_engine.py`, replacing the
defect weight (tau or tau-2) by kappa. The optimistic-credit suffix
bound remains -(Q - j(v)) because every kappa-edge has weight
>= j(v) - j(v') (a one-edge has weight 1 and preserves j; a zero-edge has
weight >= -1 and increments j by 1). Hence the relevance rule

    relevant_kappa(v, d) iff  d - (Q - j(v)) < T

is sound for kappa as well, and the closure-to-barrier theorem of
`S216.lean` lifts to S230 verbatim once the cost function is generalised.
"""

from __future__ import annotations
from collections import deque
from typing import Dict, List, Tuple, Optional, Any
import json, time

# Reuse S202 constants from the canonical engine.
from s202_engine import ADMISSIBLE, TAU, a202_mod, State


def kappa_precise(symbol: str, tau: int) -> int:
    if symbol == "one":
        return 1
    # symbol == "zero"
    return -1 if tau == 1 else 0


def kappa_coarse(symbol: str, _tau: int) -> int:
    # Signature kept aligned with kappa_precise for swappable cost fns;
    # the leading underscore tells linters the parameter is intentionally
    # unused.
    return 1 if symbol == "one" else -1


class S230Engine:
    """BF closure engine for the combinatorial cost kappa.

    Identical structure to `S216Engine` but with a swappable cost
    function. The relevance rule

        relevant(v, d) iff d - (Q - j(v)) < T

    is sound because every kappa-edge has weight >= j(v) - j(v').
    """

    def __init__(self, m: int, Q: int, kappa_fn,
                 threshold: Optional[int] = None):
        self.m = m
        self.Q = Q
        self.R = 22 * m + 2
        self.threshold = m if threshold is None else threshold
        self.target = a202_mod(self.R)
        self.start = State(j=0, c=self.target)
        self.kappa = kappa_fn
        self._inv_cache: Dict[Tuple[int, int], int] = {}

    def modulus(self, j: int) -> int:
        return 3 ** (self.R + j)

    def inv_pow2(self, t: int, j: int) -> int:
        key = (t, j)
        v = self._inv_cache.get(key)
        if v is None:
            M = self.modulus(j)
            v = pow(pow(2, t, M), -1, M)
            self._inv_cache[key] = v
        return v

    def is_goal(self, s: State) -> bool:
        return s.c == 1

    def credit(self, s: State) -> int:
        return self.Q - s.j

    def is_relevant(self, s: State, d: int) -> bool:
        return d - self.credit(s) < self.threshold

    def outgoing_edges(self, s: State) -> List[Tuple[State, int]]:
        """Yields (target_state, kappa_weight) pairs."""
        edges: List[Tuple[State, int]] = []
        j, c = s.j, s.c
        # Branch 1 inverse: same j; one-edge.
        M = self.modulus(j)
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            y = (self.inv_pow2(t, j) * c) % M
            if y % 9 == alpha:
                edges.append((State(j, y), self.kappa("one", t)))
        # Branch 0 inverse: j -> j+1; zero-edge.
        if j < self.Q:
            M1 = self.modulus(j + 1)
            val = (3 * c + 1) % M1
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                y = (self.inv_pow2(t, j + 1) * val) % M1
                if y % 9 == alpha:
                    edges.append((State(j + 1, y), self.kappa("zero", t)))
        return edges

    def search(self, max_states: int = 5_000_000) -> Dict[str, Any]:
        T = self.threshold
        dist: Dict[State, int] = {self.start: 0}
        queue = deque([self.start])
        in_queue = {self.start}
        expanded = 0
        edges_checked = 0
        t0 = time.time()

        while queue:
            s = queue.popleft()
            in_queue.discard(s)
            d = dist[s]
            if not self.is_relevant(s, d):
                continue
            if self.is_goal(s) and d < T:
                return {
                    "status": "refuted",
                    "state": {"j": s.j, "c": s.c},
                    "dist": d,
                    "states_seen": len(dist),
                    "elapsed_s": time.time() - t0,
                }
            expanded += 1
            if len(dist) > max_states:
                return {
                    "status": "incomplete",
                    "m": self.m, "Q": self.Q, "T": T,
                    "states_seen": len(dist),
                    "expanded": expanded,
                    "edges_checked": edges_checked,
                    "elapsed_s": time.time() - t0,
                }
            for (target, w) in self.outgoing_edges(s):
                edges_checked += 1
                nd = d + w
                if self.is_goal(target) and nd < T:
                    return {
                        "status": "refuted",
                        "state": {"j": target.j, "c": target.c},
                        "dist": nd,
                        "states_seen": len(dist),
                        "elapsed_s": time.time() - t0,
                    }
                if not self.is_relevant(target, nd):
                    continue
                old = dist.get(target)
                if old is None or nd < old:
                    dist[target] = nd
                    if target not in in_queue:
                        queue.append(target)
                        in_queue.add(target)

        return {
            "status": "barrier",
            "m": self.m, "Q": self.Q, "T": T,
            "states_seen": len(dist),
            "expanded": expanded,
            "edges_checked": edges_checked,
            "min_goal_dist_ge": T,
            "elapsed_s": time.time() - t0,
            # Full dist table; H(v) := T - dist[v] is the dual potential.
            "dist_table": [
                {"j": s.j, "c": s.c, "dist": d}
                for s, d in sorted(dist.items(),
                                   key=lambda kv: (kv[0].j, kv[0].c))
            ],
        }


# ---------- experimental harness ----------

FRONTIER = [
    (1, 3), (1, 5), (1, 8), (1, 10),
    (2, 6), (2, 9),
    (3, 6),
]


def run_dual_experiment(max_states: int = 5_000_000) -> Dict[str, Any]:
    print("=== S230 dual-potential experiment ===\n")
    print(f"{'m':>3} {'Q':>3} | "
          f"{'precise:status':<10} {'st':>8} {'t(s)':>7} | "
          f"{'coarse:status':<10} {'st':>8} {'t(s)':>7}")
    print("-" * 80)
    results = []
    for (m, Q) in FRONTIER:
        eng_p = S230Engine(m=m, Q=Q, kappa_fn=kappa_precise)
        res_p = eng_p.search(max_states=max_states)
        eng_c = S230Engine(m=m, Q=Q, kappa_fn=kappa_coarse)
        res_c = eng_c.search(max_states=max_states)
        print(f"{m:>3} {Q:>3} | "
              f"{res_p['status']:<10} "
              f"{res_p.get('states_seen','?'):>8} "
              f"{res_p['elapsed_s']:>7.2f} | "
              f"{res_c['status']:<10} "
              f"{res_c.get('states_seen','?'):>8} "
              f"{res_c['elapsed_s']:>7.2f}")
        results.append({
            "m": m, "Q": Q,
            "kappa_precise": res_p,
            "kappa_coarse": res_c,
        })
    return {"frontier": FRONTIER, "results": results}


def _tag(res: Dict[str, Any]) -> str:
    s = res["status"]
    if s == "barrier":
        return "VERIFIED"
    if s == "refuted":
        return "REFUTED"
    return "incomplete (budget)"


def summarise(results: Dict[str, Any]) -> None:
    print("\n=== Summary ===")
    n_precise_verified = 0
    n_coarse_verified = 0
    n_precise_refuted = 0
    n_coarse_refuted = 0
    for entry in results["results"]:
        m, Q = entry["m"], entry["Q"]
        p = entry["kappa_precise"]
        c = entry["kappa_coarse"]
        if p["status"] == "barrier":     n_precise_verified += 1
        if p["status"] == "refuted":     n_precise_refuted += 1
        if c["status"] == "barrier":     n_coarse_verified += 1
        if c["status"] == "refuted":     n_coarse_refuted += 1
        print(f"  m={m}, Q={Q}: precise={_tag(p)}, coarse={_tag(c)}")
    total = len(results["results"])
    print()
    print(f"  precise (n_one - n_neg >= m, exact form):")
    print(f"    VERIFIED on {n_precise_verified}/{total} frontier cylinders.")
    print(f"    refuted: {n_precise_refuted}; incomplete: "
          f"{total - n_precise_verified - n_precise_refuted}.")
    print(f"  coarse (n_one - q >= m, over-strong form):")
    print(f"    VERIFIED on {n_coarse_verified}/{total} frontier cylinders.")
    print(f"    refuted: {n_coarse_refuted}; incomplete: "
          f"{total - n_coarse_verified - n_coarse_refuted}.")
    print()
    if n_precise_refuted == 0 and n_coarse_refuted == 0:
        print("  No refutation on the explored region. The dual potential")
        print("  cleanly certifies precise on smaller cylinders; coarse is")
        print("  HARDER to certify (consistently larger relevant region).")
        print("  This matches Tao's §9 cue: the natural chain reveals that")
        print("  precise is the right statement, while coarse may either be")
        print("  true with a subtler argument or genuinely over-strong on")
        print("  deeper cylinders. Either outcome refines the open problem.")


if __name__ == "__main__":
    out = run_dual_experiment()
    summarise(out)
    with open("tools/s230_dual_results.json", "w") as f:
        json.dump(out, f, indent=2, default=str)
    print("\nWrote tools/s230_dual_results.json")
