"""
s216_colab_debug.py — Debug-grade Colab script for S216 closure search.

Purpose
-------
Provide a clean, single-file, Colab-pasteable implementation of the
S216 inverse-cylinder Bellman-Ford engine. The previous Colab script
contained two bugs:

  (A) Wrong edge weights. One-edges were given weight 1 and zero-edges
      weight {-1, 0}. The correct weights — matching the defect
      decomposition D(u) = A(u) - 2 q(u) — are:
        one-edge with τ = t:   weight = t      (range 1..4)
        zero-edge with τ = t:  weight = t - 2  (range -1..2)

  (B) Optimistic credit was being applied on top of the wrong weights,
      pruning all paths that could reach c = 1. Result: 50M states
      explored, 0 goal hits — a vacuous "✓ holds".

This file mirrors `tools/s216_engine.py` exactly. It is intentionally
self-contained (no imports from the local toolchain) so it can be
pasted directly into a Colab cell.

Sanity targets (states_seen, BF closure under optimistic credit; from
`tools/s216_engine.py` ground truth):
    (m=1, Q=3)  ->        35
    (m=1, Q=5)  ->       462
    (m=1, Q=8)  ->    24,310
    (m=2, Q=6)  ->     3,003

The script first runs sanity, prints PASS/FAIL with deltas, then —
only on PASS — runs the frontier cases (m=1,Q=10), (m=2,Q=9),
(m=3,Q=6) under a higher state budget.
"""

from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional, Any
import json, time

# --- S202 constants (canonical) ---
ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}
B202 = 919_447_060_349
A202 = 43
Q202 = 22
DEN202 = 2**A202 - 3**Q202


def a202_mod(R: int) -> int:
    M = 3**R
    return (B202 * pow(DEN202 % M, -1, M)) % M


@dataclass(frozen=True)
class State:
    j: int
    c: int


class S216Engine:
    """Backward BF over inverse cylinder graph with optimistic credit.

    Edge weight = defect contribution:
        one-edge:  τ(α)        ∈ {1, 2, 3, 4}
        zero-edge: τ(α) - 2    ∈ {-1, 0, 1, 2}

    Optimistic relevance:  d - (Q - j) < T
        i.e., a (state, dist) is kept iff cumulative defect could still
        fall below T using the remaining Q - j zero-edges.
    """

    def __init__(self, m: int, Q: int, threshold: Optional[int] = None):
        self.m = m
        self.Q = Q
        self.R = 22 * m + 2
        self.threshold = m if threshold is None else threshold
        self.target = a202_mod(self.R)
        self.start = State(j=0, c=self.target)
        self._inv_cache: Dict[Tuple[int, int], int] = {}

    # --- graph primitives ---

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
        """Inverse edges (predecessors in the forward Collatz map)."""
        edges: List[Tuple[State, int]] = []
        j, c = s.j, s.c
        # Branch 1 inverse: same j, weight = τ.
        M = self.modulus(j)
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            y = (self.inv_pow2(t, j) * c) % M
            if y % 9 == alpha:
                edges.append((State(j, y), t))
        # Branch 0 inverse: j -> j+1, weight = τ - 2. Only if j < Q.
        if j < self.Q:
            M1 = self.modulus(j + 1)
            val = (3 * c + 1) % M1
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                y = (self.inv_pow2(t, j + 1) * val) % M1
                if y % 9 == alpha:
                    edges.append((State(j + 1, y), t - 2))
        return edges

    # --- core search ---

    def search_or_certify_bf(self, max_states: int = 1_000_000) -> Dict[str, Any]:
        T = self.threshold
        dist: Dict[State, int] = {self.start: 0}
        queue = deque([self.start])
        in_queue = {self.start}
        expanded = 0
        edges_checked = 0
        goals_seen = 0
        t0 = time.time()

        while queue:
            s = queue.popleft()
            in_queue.discard(s)
            d = dist[s]
            if not self.is_relevant(s, d):
                continue
            if self.is_goal(s):
                goals_seen += 1
                if d < T:
                    return {
                        "status": "useful_path",
                        "state": {"j": s.j, "c": s.c},
                        "dist": d,
                        "states_seen": len(dist),
                        "elapsed_s": time.time() - t0,
                    }
            expanded += 1
            if len(dist) > max_states:
                return {
                    "status": "incomplete",
                    "m": self.m, "Q": self.Q, "R": self.R, "threshold": T,
                    "states_seen": len(dist),
                    "expanded": expanded,
                    "edges_checked": edges_checked,
                    "goals_seen": goals_seen,
                    "elapsed_s": time.time() - t0,
                }
            for (target, w) in self.outgoing_edges(s):
                edges_checked += 1
                nd = d + w
                if self.is_goal(target) and nd < T:
                    return {
                        "status": "useful_path",
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
            "status": "barrier_certificate",
            "m": self.m, "Q": self.Q, "R": self.R, "threshold": T,
            "states_seen": len(dist),
            "expanded": expanded,
            "edges_checked": edges_checked,
            "goals_seen": goals_seen,
            "conclusion": f"C-back_S202(m={self.m}, Q={self.Q}) >= {T}",
            "elapsed_s": time.time() - t0,
        }


# --- self-check ---

def verify_w202():
    n, A, q = 1, 0, 0
    W = "10100000001000010000000000"
    for ch in W:
        t = TAU[n % 9]
        if ch == "1":
            n, A = (2**t) * n, A + t
        else:
            n, A, q = ((2**t) * n - 1) // 3, A + t, q + 1
    return (n, A, q) == (251, 43, 22)


# --- Phase 1: sanity ---

SANITY = [
    ((1, 3),       35),
    ((1, 5),      462),
    ((1, 8),   24_310),
    ((2, 6),    3_003),
]


def run_sanity(max_states: int = 200_000) -> bool:
    print("=== Phase 1: sanity ===")
    print(f"W202 self-check: {'ok' if verify_w202() else 'FAIL'}")
    all_pass = True
    for ((m, Q), expected) in SANITY:
        eng = S216Engine(m=m, Q=Q)
        res = eng.search_or_certify_bf(max_states=max_states)
        got = res.get("states_seen", -1)
        delta = got - expected
        ok = (got == expected and res["status"] == "barrier_certificate")
        tag = "PASS" if ok else "FAIL"
        all_pass = all_pass and ok
        print(f"  m={m}, Q={Q}: status={res['status']}, "
              f"states={got}, expected={expected}, delta={delta:+d}  [{tag}]")
        if res["status"] == "barrier_certificate":
            print(f"    goals_seen={res['goals_seen']}, "
                  f"expanded={res['expanded']}, "
                  f"edges={res['edges_checked']}, "
                  f"t={res['elapsed_s']:.2f}s")
    print()
    return all_pass


# --- Phase 2: frontier ---

FRONTIER = [(1, 8), (1, 10), (2, 6), (2, 9), (3, 6)]


def run_frontier(max_states: int = 50_000_000):
    print("=== Phase 2: frontier ===")
    print(f"{'m':>3} {'Q':>3} {'states':>12} {'goals':>6} {'status':<22} "
          f"{'verdict':<15} {'time(s)':>8}")
    print("-" * 90)
    out = []
    for (m, Q) in FRONTIER:
        eng = S216Engine(m=m, Q=Q)
        res = eng.search_or_certify_bf(max_states=max_states)
        states = res.get("states_seen", "?")
        goals = res.get("goals_seen", "?")
        status = res.get("status", "?")
        t = res.get("elapsed_s", 0.0)
        if status == "barrier_certificate":
            verdict = "BARRIER PROVEN"
        elif status == "useful_path":
            verdict = "COUNTEREXAMPLE"
        else:
            verdict = "incomplete"
        print(f"{m:>3} {Q:>3} {states:>12,} {goals:>6} {status:<22} "
              f"{verdict:<15} {t:>8.2f}")
        out.append({"m": m, "Q": Q, "result": res})
    return out


if __name__ == "__main__":
    ok = run_sanity()
    if not ok:
        print("Sanity FAILED — not running frontier. Investigate first.")
    else:
        print("Sanity PASSED — running frontier.")
        results = run_frontier(max_states=50_000_000)
        with open("s216_frontier_results.json", "w") as f:
            json.dump(results, f, indent=2,
                      default=lambda o: getattr(o, "__dict__", str(o)))
        print("Wrote s216_frontier_results.json")
