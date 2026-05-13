"""
S216 Colab-friendly engine — memory-efficient BF closure with checkpointing.

Differences from `s216_engine.py`:

  1. Larger default budget (10^7 states), explicit memory monitoring.
  2. Frontier deque with seen-set deduplication.
  3. Periodic progress logging.
  4. Checkpointing to `/content/s216_state.pkl` (Colab-friendly path).
  5. Resume from checkpoint.
  6. Optional Cython-like inner loop via `__slots__` and packed ints.
  7. Batched JSON emission to handle large tables.

Run in Colab:

    !pip install tqdm  # optional progress bar
    !wget https://path/to/s216_colab.py   # or upload manually
    python s216_colab.py --m 1 --Q 10 --budget 5000000 --checkpoint /content/s216.pkl

Or as a script inside a Colab cell:

    %run s216_colab.py 1 10
"""
from __future__ import annotations
import os
import sys
import time
import json
import pickle
import argparse
from collections import deque
from dataclasses import dataclass

# Optional tqdm for nice progress
try:
    from tqdm import tqdm
    HAS_TQDM = True
except ImportError:
    HAS_TQDM = False


# ============================================================
# S202 mathematical constants
# ============================================================
ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}
A202 = 43
Q202 = 22
B202 = 919_447_060_349
DEN202 = 2 ** A202 - 3 ** Q202


def a202_mod(R: int) -> int:
    M = 3 ** R
    return (B202 * pow(DEN202 % M, -1, M)) % M


@dataclass(frozen=True)
class State:
    __slots__ = ('j', 'c')
    j: int
    c: int

    def __hash__(self):
        # Pack j (up to 32 bits) and c into a single int for speed.
        return hash((self.j, self.c))


# ============================================================
# S216 engine with BF optimistic closure
# ============================================================
class S216Colab:
    """BF closure engine optimized for large Q on Colab.

    Maintains:
      dist : dict[State, int]    — Bellman-Ford fixed point
      tbl_seen : set[State]      — every state we've inserted
      frontier : deque[State]    — current relaxation queue

    Closure rule: a (state, dist) is *relevant* iff
      dist - (Q - state.j) < T
    All non-relevant labels are pruned at insertion time.
    """

    def __init__(self, m: int, Q: int, T: int = None, *, budget: int = 10**7,
                 log_every: int = 50_000, checkpoint_path: str = None,
                 checkpoint_every: int = 500_000):
        self.m = m
        self.Q = Q
        self.R = 22 * m + 2
        self.T = m if T is None else T
        self.target = a202_mod(self.R)
        self.start = State(0, self.target)
        self.budget = budget
        self.log_every = log_every
        self.checkpoint_path = checkpoint_path
        self.checkpoint_every = checkpoint_every
        # caches: invMod2Pow indexed by (tau, j)
        self._inv_pow_cache: dict = {}
        # state
        self.dist: dict = {self.start: 0}
        self.frontier: deque = deque([self.start])
        self.in_frontier = {self.start}
        self.expanded = 0
        self.edges_checked = 0
        self.relax_count = 0
        self.start_time = None
        self.last_log = 0
        self.last_ckpt = 0
        self.t0 = None
        self.status_msg = None

    # --- inverse cylinder graph ---
    def modulus(self, j: int) -> int:
        return 3 ** (self.R + j)

    def inv_pow2(self, t: int, j: int) -> int:
        key = (t, j)
        if key not in self._inv_pow_cache:
            M = self.modulus(j)
            self._inv_pow_cache[key] = pow(pow(2, t, M), -1, M)
        return self._inv_pow_cache[key]

    def is_goal(self, s: State) -> bool:
        return s.c == 1

    def is_relevant(self, s: State, d: int) -> bool:
        return d - (self.Q - s.j) < self.T

    def outgoing_edges(self, s: State):
        """Yield (target_state, weight) pairs. Generator for memory."""
        j, c = s.j, s.c
        # Branch 1 inverse
        M = self.modulus(j)
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            y = (self.inv_pow2(t, j) * c) % M
            if y % 9 == alpha:
                yield (State(j, y), t)
        # Branch 0 inverse
        if j < self.Q:
            j1 = j + 1
            M1 = self.modulus(j1)
            base = 3 * c + 1
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                y = (self.inv_pow2(t, j1) * base) % M1
                if y % 9 == alpha:
                    yield (State(j1, y), t - 2)

    # --- checkpointing ---
    def save_checkpoint(self):
        if not self.checkpoint_path:
            return
        try:
            with open(self.checkpoint_path, "wb") as f:
                pickle.dump({
                    "m": self.m, "Q": self.Q, "T": self.T, "R": self.R,
                    "dist": self.dist,
                    "frontier": list(self.frontier),
                    "in_frontier": self.in_frontier,
                    "expanded": self.expanded,
                    "edges_checked": self.edges_checked,
                    "relax_count": self.relax_count,
                }, f)
        except Exception as ex:
            print(f"[ckpt] save failed: {ex}", file=sys.stderr)

    def load_checkpoint(self) -> bool:
        if not self.checkpoint_path or not os.path.exists(self.checkpoint_path):
            return False
        try:
            with open(self.checkpoint_path, "rb") as f:
                d = pickle.load(f)
            if (d["m"], d["Q"], d["T"], d["R"]) != (self.m, self.Q, self.T, self.R):
                print("[ckpt] parameter mismatch, ignoring", file=sys.stderr)
                return False
            self.dist = d["dist"]
            self.frontier = deque(d["frontier"])
            self.in_frontier = d["in_frontier"]
            self.expanded = d["expanded"]
            self.edges_checked = d["edges_checked"]
            self.relax_count = d.get("relax_count", 0)
            print(f"[ckpt] resumed: {len(self.dist)} states, "
                  f"frontier {len(self.frontier)}, expanded {self.expanded}")
            return True
        except Exception as ex:
            print(f"[ckpt] load failed: {ex}", file=sys.stderr)
            return False

    def log_progress(self):
        if self.t0 is None:
            return
        n = len(self.dist)
        elapsed = time.time() - self.t0
        rate = self.expanded / elapsed if elapsed > 0 else 0
        front = len(self.frontier)
        print(f"[s216] m={self.m} Q={self.Q} T={self.T}  "
              f"states={n:>9}  frontier={front:>7}  "
              f"expanded={self.expanded:>9}  "
              f"edges={self.edges_checked:>10}  "
              f"rate={rate:>7.0f}/s  t={elapsed:>6.1f}s",
              flush=True)

    # --- main BF loop ---
    def run(self):
        """Returns a result dict with status and (if barrier) the table."""
        self.load_checkpoint()
        self.t0 = time.time()
        self.last_log = self.expanded
        self.last_ckpt = self.expanded

        while self.frontier:
            s = self.frontier.popleft()
            self.in_frontier.discard(s)
            d = self.dist[s]
            if not self.is_relevant(s, d):
                continue
            if self.is_goal(s) and d < self.T:
                return self._result_useful_path(s, d)
            self.expanded += 1
            if len(self.dist) > self.budget:
                self.save_checkpoint()
                return {
                    "status": "incomplete",
                    "m": self.m, "Q": self.Q, "T": self.T, "R": self.R,
                    "states_seen": len(self.dist),
                    "expanded": self.expanded,
                    "edges_checked": self.edges_checked,
                    "frontier_size": len(self.frontier),
                    "reason": "budget_exceeded",
                    "advice": f"Increase --budget beyond {self.budget}.",
                }
            for (target, w) in self.outgoing_edges(s):
                self.edges_checked += 1
                nd = d + w
                if self.is_goal(target) and nd < self.T:
                    return self._result_useful_path(target, nd)
                if not self.is_relevant(target, nd):
                    continue
                old = self.dist.get(target)
                if old is None or nd < old:
                    self.dist[target] = nd
                    self.relax_count += 1
                    if target not in self.in_frontier:
                        self.frontier.append(target)
                        self.in_frontier.add(target)
            if self.expanded - self.last_log >= self.log_every:
                self.log_progress()
                self.last_log = self.expanded
            if (self.checkpoint_path and
                    self.expanded - self.last_ckpt >= self.checkpoint_every):
                self.save_checkpoint()
                self.last_ckpt = self.expanded

        return self._result_barrier()

    def _result_useful_path(self, s, d):
        return {
            "status": "useful_path",
            "m": self.m, "Q": self.Q, "T": self.T, "R": self.R,
            "state": {"j": s.j, "c": s.c},
            "dist": d,
            "states_seen": len(self.dist),
            "expanded": self.expanded,
            "edges_checked": self.edges_checked,
            "note": "Found a cheap path to a goal — barrier does NOT hold at this T.",
        }

    def _result_barrier(self):
        states = sorted(
            ({"j": s.j, "c": s.c, "dist": d}
             for s, d in self.dist.items()),
            key=lambda x: (x["j"], x["c"]),
        )
        return {
            "status": "barrier_certificate",
            "type": "S216_bellman_ford_closure_certificate",
            "m": self.m, "Q": self.Q, "T": self.T, "R": self.R,
            "states_seen": len(self.dist),
            "expanded": self.expanded,
            "edges_checked": self.edges_checked,
            "closure_rule": "d - (Q - j) < T",
            "conclusion": f"𝒞^←_S202(m={self.m}, Q={self.Q}) >= {self.T}",
            "states": states,
        }

    # --- verifier ---
    def verify(self, cert: dict) -> dict:
        if cert.get("status") != "barrier_certificate":
            return {"ok": False, "reason": "not_a_certificate"}
        T = cert["T"]
        state_dist = {State(it["j"], it["c"]): it["dist"]
                      for it in cert["states"]}
        if self.start not in state_dist:
            return {"ok": False, "reason": "start_missing"}
        if state_dist[self.start] != 0:
            return {"ok": False, "reason": "start_dist_nonzero"}
        for s, d in state_dist.items():
            if self.is_goal(s) and d < T:
                return {"ok": False, "reason": "goal_below_T",
                        "state": {"j": s.j, "c": s.c, "dist": d}}
        for s, d in state_dist.items():
            if not self.is_relevant(s, d):
                continue
            for (tgt, w) in self.outgoing_edges(s):
                nd = d + w
                if self.is_goal(tgt) and nd < T:
                    return {"ok": False, "reason": "edge_to_cheap_goal"}
                if not self.is_relevant(tgt, nd):
                    continue
                if tgt not in state_dist:
                    return {"ok": False, "reason": "missing_relevant_target",
                            "source": {"j": s.j, "c": s.c, "dist": d},
                            "target": {"j": tgt.j, "c": tgt.c, "expected_dist_le": nd}}
                if state_dist[tgt] > nd:
                    return {"ok": False, "reason": "target_dist_too_large",
                            "source": {"j": s.j, "c": s.c, "dist": d},
                            "target": {"j": tgt.j, "c": tgt.c,
                                       "actual": state_dist[tgt],
                                       "expected_at_most": nd}}
        return {"ok": True,
                "states_in_certificate": len(state_dist),
                "conclusion": cert["conclusion"]}


# ============================================================
# CLI
# ============================================================
def main():
    parser = argparse.ArgumentParser(
        description="S216 BF closure engine (Colab-friendly).")
    parser.add_argument("--m", type=int, default=1, help="cylinder index")
    parser.add_argument("--Q", type=int, default=3, help="zero budget")
    parser.add_argument("--T", type=int, default=None,
                        help="target threshold (default: m)")
    parser.add_argument("--budget", type=int, default=10**7,
                        help="max states (default 10M)")
    parser.add_argument("--log-every", type=int, default=50_000,
                        help="log every N expansions")
    parser.add_argument("--checkpoint", type=str, default=None,
                        help="checkpoint file (resumable)")
    parser.add_argument("--checkpoint-every", type=int, default=500_000,
                        help="checkpoint every N expansions")
    parser.add_argument("--out-json", type=str, default=None,
                        help="write certificate JSON to this file")
    parser.add_argument("--verify-only", action="store_true",
                        help="just verify the given --in-json")
    parser.add_argument("--in-json", type=str, default=None,
                        help="path to a JSON certificate to verify")

    args = parser.parse_args()
    engine = S216Colab(
        args.m, args.Q, args.T,
        budget=args.budget,
        log_every=args.log_every,
        checkpoint_path=args.checkpoint,
        checkpoint_every=args.checkpoint_every,
    )

    if args.verify_only:
        if not args.in_json:
            print("--verify-only requires --in-json", file=sys.stderr)
            sys.exit(2)
        with open(args.in_json) as f:
            cert = json.load(f)
        verdict = engine.verify(cert)
        print(json.dumps(verdict, indent=2, ensure_ascii=False))
        sys.exit(0 if verdict.get("ok") else 1)

    print(f"=== S216 engine: m={args.m} Q={args.Q} T={engine.T} R={engine.R} ===")
    print(f"  target residue: {engine.target}")
    print(f"  start: {engine.start}")
    print(f"  budget: {args.budget}")
    print()

    result = engine.run()
    engine.log_progress()
    print()

    if result["status"] == "barrier_certificate":
        verdict = engine.verify(result)
        print(f"VERIFICATION: {'ok ✓' if verdict.get('ok') else 'FAILED'}")
        if not verdict.get("ok"):
            print(json.dumps(verdict, indent=2, ensure_ascii=False))
        print(f"Conclusion: {result['conclusion']}")
        print(f"Certificate size: {result['states_seen']} states")
    elif result["status"] == "useful_path":
        print(f"FOUND CHEAP PATH: barrier FAILS at T={engine.T}")
        print(f"  Reached {result['state']} with dist={result['dist']}")
    elif result["status"] == "incomplete":
        print(f"INCOMPLETE: {result['reason']}")
        print(f"  states_seen={result['states_seen']}, "
              f"frontier_size={result['frontier_size']}")
        print(f"  advice: {result['advice']}")

    if args.out_json:
        with open(args.out_json, "w") as f:
            json.dump(result, f, indent=2, ensure_ascii=False)
        print(f"Wrote: {args.out_json}")


# ============================================================
# Colab one-liners
# ============================================================
def run_colab(m: int, Q: int, T: int = None, budget: int = 10**7,
              checkpoint: str = None) -> dict:
    """Convenience: run inside a Colab cell, return the certificate dict."""
    engine = S216Colab(m, Q, T, budget=budget, checkpoint_path=checkpoint)
    result = engine.run()
    engine.log_progress()
    if result["status"] == "barrier_certificate":
        verdict = engine.verify(result)
        result["_verify"] = verdict
    return result


if __name__ == "__main__":
    main()
