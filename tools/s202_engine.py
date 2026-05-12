"""
S202Engine — Backward DFS over the inverse cylinder graph.

Produces closure-style barrier certificates: an exhaustive enumeration
of the "cheap region" (states reachable from `aS202 (mod 3^R)` with
total inverse-path cost < threshold).

If no goal vertex (cylinder containing `1`) appears in the cheap region,
the certificate proves:

  𝒞^←_{S202}(m, Q) ≥ threshold

i.e., no admissible word `u` with `q(u) ≤ Q` and `n(u) ≡ aS202
(mod 3^(22m+2))` has defect `D(u) < threshold`.

The certificate JSON is liftable to a Lean theorem via the
`CollatzLean4.Admissible.Cert_*` modules in the main Lean project
(see `CollatzLean4/CollatzLean4/Cert_m1_Q3.lean` for an example).

Reference: Andújar Mata, "S202–S217 admissible inverse program" (2026).
"""

from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from typing import Dict, Tuple, Optional, List, Any
import json


# --- S202 constants ---
ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}
W202 = "10100000001000010000000000"
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


class S202Engine:
    """Backward DFS over the inverse cylinder graph."""

    def __init__(self, m: int, Q: int, threshold: Optional[int] = None):
        self.m = m
        self.Q = Q
        self.R = 22 * m + 2
        self.threshold = m if threshold is None else threshold
        self.target = a202_mod(self.R)
        self.start = State(j=0, c=self.target)
        self._inv_cache: Dict[Tuple[int, int], int] = {}

    def modulus(self, j: int) -> int:
        return 3 ** (self.R + j)

    def inv_pow2(self, t: int, j: int) -> int:
        key = (t, j)
        if key not in self._inv_cache:
            M = self.modulus(j)
            self._inv_cache[key] = pow(pow(2, t, M), -1, M)
        return self._inv_cache[key]

    def is_goal(self, s: State) -> bool:
        return s.c == 1

    def outgoing_edges(self, s: State) -> List[Tuple[State, int]]:
        """Yields (target_state, edge_weight) pairs."""
        edges = []
        j, c = s.j, s.c
        # Branch 1 inverse: same j, weight τ(α).
        M = self.modulus(j)
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            y = (self.inv_pow2(t, j) * c) % M
            if y % 9 == alpha:
                edges.append((State(j, y), t))
        # Branch 0 inverse: j → j+1, weight τ(α) - 2. Only if j < Q.
        if j < self.Q:
            M1 = self.modulus(j + 1)
            val = (3 * c + 1) % M1
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                y = (self.inv_pow2(t, j + 1) * val) % M1
                if y % 9 == alpha:
                    edges.append((State(j + 1, y), t - 2))
        return edges

    def search_or_certify(self, max_states: int = 1_000_000) -> Dict[str, Any]:
        """
        Returns:
          {"status": "useful_path", ...}    -- found a goal with cost < T
          {"status": "barrier_certificate", "states": [{j,c,dist}, ...]}
          {"status": "incomplete", ...}     -- ran out of state budget
        """
        T = self.threshold
        dist: Dict[State, int] = {self.start: 0}
        queue = deque([self.start])
        in_queue = {self.start}

        while queue:
            s = queue.popleft()
            in_queue.discard(s)
            d = dist[s]
            if d >= T:
                continue
            if self.is_goal(s):
                return {"status": "useful_path", "state": s, "dist": d}

            if len(dist) > max_states:
                return {
                    "status": "incomplete",
                    "states_seen": len(dist),
                    "message": "max_states_exceeded",
                }

            for (target, w) in self.outgoing_edges(s):
                nd = d + w
                if nd >= T:
                    continue
                old = dist.get(target)
                if old is None or nd < old:
                    dist[target] = nd
                    if target not in in_queue:
                        queue.append(target)
                        in_queue.add(target)

        # No goal found: produce barrier certificate
        states = sorted(
            ({"j": s.j, "c": s.c, "dist": d} for s, d in dist.items()),
            key=lambda x: (x["j"], x["c"]),
        )
        return {
            "status": "barrier_certificate",
            "m": self.m,
            "Q": self.Q,
            "R": self.R,
            "threshold": T,
            "states_seen": len(dist),
            "states": states,
            "conclusion": f"𝒞^←_{{S202}}(m={self.m}, Q={self.Q}) ≥ {T}",
        }


def verify_w202():
    """Sanity check: evalWord W202 from n=1 gives (n=251, A=43, q=22, D=−1)."""
    n, A, q = 1, 0, 0
    for ch in W202:
        t = TAU[n % 9]
        if ch == "1":
            n, A = (2**t) * n, A + t
        else:
            n, A, q = ((2**t) * n - 1) // 3, A + t, q + 1
    return {"n": n, "A": A, "q": q, "D": A - 2 * q,
            "ok": (n, A, q) == (251, 43, 22)}


if __name__ == "__main__":
    print("W202 verification:", verify_w202())
    print()
    for (m, Q) in [(1, 3), (1, 5), (1, 8), (1, 10), (2, 6)]:
        print(f"=== m={m}, Q={Q} ===")
        engine = S202Engine(m=m, Q=Q)
        result = engine.search_or_certify(max_states=200_000)
        print(f"  status: {result['status']}")
        if result["status"] == "barrier_certificate":
            print(f"  states: {result['states_seen']}")
            print(f"  conclusion: {result['conclusion']}")
        elif result["status"] == "incomplete":
            print(f"  states explored: {result['states_seen']}")
