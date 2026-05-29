"""
kappa_precise_probe.py — Decisive experiment for the κ-precise barrier.

κ-precise edge weights (from `InvKappaPreciseEdge` in AnalyticBarrier.lean):
    one-edge            : κ = +1
    zero-edge, τ(c')=1  : κ = -1
    zero-edge, τ(c')≥2  : κ =  0
Total κ along a path = (#one-edges) − (#τ=1 zero-edges) = n_one − n_neg.

`S202_kappa_precise_barrier_bounded m Q` holds  ⇔  every start→goal path in the
slice j ≤ Q has total κ ≥ m  ⇔  min κ-cost(start→goal) ≥ m.

We answer this with the SAME Bellman-Ford optimistic-cut engine used for the
verified defect certificates (`S216Engine`): the maximum future κ-decrease from
depth j is (Q − j) (each remaining zero-step is at most −1, exactly as for the
actual defect weights), so the optimistic cut `d − (Q − j) < T` is valid for κ.

Running with threshold T = m:
  status "barrier_certificate" → no goal with κ-cost < m → barrier HOLDS (≥ m).
  status "useful_path"         → a goal with κ-cost < m → barrier FAILS  (DEAD END).
"""

from __future__ import annotations
from typing import List, Tuple, Dict, Any
from s202_engine import State, ADMISSIBLE, TAU
from s216_engine import S216Engine


class KappaEngine(S216Engine):
    """S216 optimistic-cut Bellman-Ford with κ-precise edge weights."""

    def outgoing_edges(self, s: State) -> List[Tuple[State, int]]:
        edges: List[Tuple[State, int]] = []
        j, c = s.j, s.c
        M = self.modulus(j)
        # one-edges: same j, κ = +1
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            y = (self.inv_pow2(t, j) * c) % M
            if y % 9 == alpha:
                edges.append((State(j, y), 1))
        # zero-edges: j+1, κ = -1 if τ==1 else 0
        if j < self.Q:
            M1 = self.modulus(j + 1)
            val = (3 * c + 1) % M1
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                y = (self.inv_pow2(t, j + 1) * val) % M1
                if y % 9 == alpha:
                    edges.append((State(j + 1, y), -1 if t == 1 else 0))
        return edges


def min_kappa_to_goal(m: int, Q: int, T_max: int = 6, max_states: int = 400_000):
    """Find the exact min κ-cost(start→goal) by scanning thresholds T=1..T_max.

    The largest T for which the run is a barrier_certificate equals the min
    κ-cost (since a barrier at T means min ≥ T, a witness at T means min < T)."""
    results = {}
    min_kappa = None
    for T in range(1, T_max + 1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        res = eng.search_or_certify_bf(max_states=max_states)
        results[T] = res["status"]
        if res["status"] == "useful_path":
            # found a goal with κ-cost = res["dist"] < T
            min_kappa = res["dist"]
            return min_kappa, results, res
        if res["status"] == "incomplete":
            return None, results, res
    # barrier held for all T up to T_max → min κ ≥ T_max
    return (">=%d" % T_max), results, None


def probe(m: int, Q: int):
    eng = KappaEngine(m=m, Q=Q, threshold=m)
    res = eng.search_or_certify_bf(max_states=400_000)
    print(f"=== m={m}, Q={Q}  (R={eng.R}, threshold T=m={m}) ===")
    print(f"  status: {res['status']}   states_seen={res.get('states_seen','?')}")
    if res["status"] == "barrier_certificate":
        print(f"  → κ-precise barrier HOLDS: min(n_one - n_neg) ≥ {m}  ✓")
    elif res["status"] == "useful_path":
        print(f"  → κ-precise barrier FAILS: goal at κ-cost {res['dist']} < {m}")
        print(f"     witness goal: {res['state']}   *** DEAD END for κ route ***")
    else:
        print(f"  → inconclusive: {res}")
    # exact strength
    mk, table, _ = min_kappa_to_goal(m, Q)
    print(f"  min κ-cost(start→goal) = {mk}    (threshold scan: {table})")
    return res


if __name__ == "__main__":
    for Q in [1, 2, 3, 5, 8]:
        probe(1, Q)
        print()
