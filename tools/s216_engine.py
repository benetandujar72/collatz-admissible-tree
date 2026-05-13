"""
S216 Bellman-Ford engine — closure-to-barrier with optimistic credit.

Differs from `s202_engine.py` in the closure rule: a state-label pair
(v, d) is *relevant* iff

    d - credit(v) < T,        where  credit(v) := Q - j(v)

i.e., it could *still* complete to a goal at cost < T using the
remaining (Q - j(v)) negative-edge zeros. The naive `d < T` cut is
incorrect because negative edges (zero-edges with τ = 1, contributing
weight −1) can lower cumulative cost.

Both the BFS frontier and the edge generator MUST use the optimistic
cut for the produced certificate to imply a formal barrier.

This is the engine that the Lean `S216_closure_to_barrier` theorem
will consume.
"""
from __future__ import annotations
from collections import deque
from typing import Dict, Any
import sys

# reuse types and constants
from s202_engine import State, S202Engine, ADMISSIBLE, TAU


class S216Engine(S202Engine):
    """Backward DFS using S216 optimistic closure."""

    def credit(self, s: State) -> int:
        """Maximum possible future cost decrease from state s."""
        return self.Q - s.j

    def is_relevant(self, s: State, d: int) -> bool:
        """A (state, dist) is relevant if cost can still drop below T."""
        return d - self.credit(s) < self.threshold

    def search_or_certify_bf(self, max_states: int = 1_000_000) -> Dict[str, Any]:
        """Bellman-Ford closure with optimistic relevance.

        Closure invariant produced:
          For every (s, d) in dist with is_relevant(s, d),
          for every outgoing edge (s -> v, ω):
            either is_relevant(v, d+ω) is false,
            or v in dist with dist[v] ≤ d+ω.
          Additionally: dist[start] = 0, no goal has dist < T.
        """
        T = self.threshold
        dist: Dict[State, int] = {self.start: 0}
        queue = deque([self.start])
        in_queue = {self.start}
        expanded = 0
        edges_checked = 0

        while queue:
            s = queue.popleft()
            in_queue.discard(s)
            d = dist[s]
            # Optimistic cut: only expand relevant states.
            if not self.is_relevant(s, d):
                continue
            # Positive witness check.
            if self.is_goal(s) and d < T:
                return {
                    "status": "useful_path",
                    "state": {"j": s.j, "c": s.c},
                    "dist": d,
                }
            expanded += 1
            if len(dist) > max_states:
                return {
                    "status": "incomplete",
                    "m": self.m, "Q": self.Q, "R": self.R, "threshold": T,
                    "states_seen": len(dist),
                    "expanded": expanded,
                    "edges_checked": edges_checked,
                }
            for (target, w) in self.outgoing_edges(s):
                edges_checked += 1
                nd = d + w
                if self.is_goal(target) and nd < T:
                    return {
                        "status": "useful_path",
                        "state": {"j": target.j, "c": target.c},
                        "dist": nd,
                    }
                # Only keep relevant target labels.
                if not self.is_relevant(target, nd):
                    continue
                old = dist.get(target)
                if old is None or nd < old:
                    dist[target] = nd
                    if target not in in_queue:
                        queue.append(target)
                        in_queue.add(target)

        # All explored, no cheap goal: produce barrier certificate.
        states = sorted(
            (
                {
                    "j": s.j, "c": s.c, "dist": d,
                    "credit": self.credit(s),
                    "optimistic": d - self.credit(s),
                }
                for s, d in dist.items()
            ),
            key=lambda x: (x["j"], x["c"]),
        )
        return {
            "status": "barrier_certificate",
            "type": "S216_bellman_ford_closure_certificate",
            "m": self.m, "Q": self.Q, "R": self.R, "threshold": T,
            "states_seen": len(dist),
            "expanded": expanded,
            "edges_checked": edges_checked,
            "closure_rule": "d - (Q - j) < T",
            "conclusion": f"𝒞^←_{{S202}}(m={self.m}, Q={self.Q}) ≥ {T}",
            "states": states,
        }

    def verify_bf_closure(self, cert: Dict[str, Any]) -> Dict[str, Any]:
        """Independent verifier for an S216 closure certificate."""
        if cert.get("status") != "barrier_certificate":
            return {"ok": False, "reason": "Not a barrier certificate."}
        T = cert["threshold"]
        state_dist: Dict[State, int] = {}
        for item in cert["states"]:
            state_dist[State(j=item["j"], c=item["c"])] = item["dist"]
        if self.start not in state_dist:
            return {"ok": False, "reason": "Start missing."}
        if state_dist[self.start] != 0:
            return {"ok": False, "reason": "Start distance ≠ 0."}
        # No cheap goal in table.
        for s, d in state_dist.items():
            if self.is_goal(s) and d < T:
                return {"ok": False, "reason": "Goal with dist < T.",
                        "state": {"j": s.j, "c": s.c, "dist": d}}
        # Optimistic closure check.
        for s, d in state_dist.items():
            if not self.is_relevant(s, d):
                continue
            for (target, w) in self.outgoing_edges(s):
                nd = d + w
                if self.is_goal(target) and nd < T:
                    return {"ok": False,
                            "reason": "Outgoing edge reaches cheap goal.",
                            "source": {"j": s.j, "c": s.c, "dist": d},
                            "target": {"j": target.j, "c": target.c,
                                       "dist": nd}}
                if not self.is_relevant(target, nd):
                    continue
                if target not in state_dist:
                    return {"ok": False,
                            "reason": "Closure failure: relevant target missing.",
                            "source": {"j": s.j, "c": s.c, "dist": d},
                            "target": {"j": target.j, "c": target.c,
                                       "dist": nd}}
                if state_dist[target] > nd:
                    return {"ok": False,
                            "reason": "Closure failure: target dist too large.",
                            "source": {"j": s.j, "c": s.c, "dist": d},
                            "target": {"j": target.j, "c": target.c,
                                       "expected_at_most": nd,
                                       "actual": state_dist[target]}}
        return {"ok": True,
                "message": "S216 BF closure certificate verified.",
                "conclusion": cert["conclusion"]}


if __name__ == "__main__":
    cases = [(1, 3), (1, 5), (1, 8), (1, 10), (2, 6)]
    print(f"{'m':>3} {'Q':>3}   {'old_states':>10}  {'s216_states':>11}  "
          f"{'status':<22}  verify")
    print("-" * 80)
    for (m, Q) in cases:
        old_engine = S202Engine(m=m, Q=Q)
        old_res = old_engine.search_or_certify(max_states=200_000)
        old_states = old_res.get("states_seen", "?")
        s216_engine = S216Engine(m=m, Q=Q)
        s216_res = s216_engine.search_or_certify_bf(max_states=200_000)
        s216_states = s216_res.get("states_seen", "?")
        status = s216_res.get("status", "?")
        if status == "barrier_certificate":
            v = s216_engine.verify_bf_closure(s216_res)
            verify = "ok ✓" if v.get("ok") else "FAIL: " + v.get("reason", "?")
        elif status == "useful_path":
            verify = f"witness path at dist={s216_res.get('dist','?')}"
        else:
            verify = s216_res.get("status", "?")
        print(f"{m:>3} {Q:>3}   {old_states:>10}  {s216_states:>11}  "
              f"{status:<22}  {verify}")
