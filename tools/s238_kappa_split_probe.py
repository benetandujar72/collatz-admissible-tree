"""
s238_kappa_split_probe.py — TRUTH PROBE for BlockBoundaryExists (the κ₂ balance).

CONTEXT
-------
The committed reduction (KappaSplitReduction.lean) leaves a single open core:

  BlockBoundaryExists m Q :  every level-(m+1) κ-path InvStart(m+1) → (m+1)-goal
  admits a split at some `mid` with
      • projπ m mid is an m-goal           (m-precision: mid.c ≡ 1 mod 3^(22m+2+mid.j))
      • mid.j ≤ Q
      • the suffix mid → goal has κ₂ ≥ 1   (κ = #one-edges − #τ1-zero-edges)

Edge κ-weights (InvKappaPreciseEdge): one-edge +1, τ=1 zero −1, τ≥2 zero 0.

This probe tests the proposed proof strategy:
  "take mid = FIRST m-precision point; the suffix to the goal has κ₂ ≥ 1,
   because τ=1 zero-edges destroy precision."

INTRACTABILITY OF THE TRUE GRAPH
--------------------------------
A genuine (m+1)-goal in the real S202 graph needs c ≡ 1 mod 3^(22(m+1)+2+j),
i.e. ν₃(c−1) ≳ 22(m+1)+2 ≈ 46 digits; reaching it costs ≈ 3^21 one-edges
(the discrete-log lower bound, structure_probe.dlog_lower_bound). So the
real start→goal path is astronomically long and CANNOT be enumerated.

We therefore run a SYNTHETIC ANALOG that preserves the exact transition
structure (same TAU table, same inverse-edge congruences, same κ-weights)
but at a SMALL base precision, with "precision levels" defined by a tunable
digit gap g (analog of the 22-digit jump per m-level). Concretely:

  base R0 (small),  "m-goal"  := c ≡ 1 mod 3^(R0+j)          [coarse]
                    "(m+1)-goal":= c ≡ 1 mod 3^(R0+g+j)      [fine, g digits deeper]

The graph is the inverse cylinder graph at the FINE precision R0+g (so edges
are well-defined to full fine depth). Start = a non-goal cylinder. We BFS to
enumerate ALL fine-goals reachable within a cost/length budget, reconstruct
actual paths, and for each path test the split claim with mid = first
m(=coarse)-precision point.

We ALSO directly verify the structural lemma the argument rests on:
  (L) the target of every τ=1 (and τ=3) zero-edge has c ≡ 2 (mod 3),
      hence is NOT coarse-precise and NOT fine-precise.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from typing import Optional
from s202_engine import ADMISSIBLE, TAU


def nu3(x: int) -> int:
    if x == 0:
        return 10**9
    x = abs(x)
    k = 0
    while x % 3 == 0:
        x //= 3
        k += 1
    return k


def kappa_weight(t: int, is_zero_edge: bool) -> int:
    """κ-precise edge weight: one-edge +1; τ=1 zero −1; τ≥2 zero 0."""
    if not is_zero_edge:
        return 1
    return -1 if t == 1 else 0


@dataclass(frozen=True)
class V:
    j: int
    c: int


class SynthGraph:
    """Inverse cylinder graph at FINE base precision Rfine = R0 + g.

    Coarse precision is R0 (g digits shallower) — the analog of the 22-digit
    per-level gap. start_c is a chosen non-goal residue at fine depth.
    """

    def __init__(self, R0: int, g: int, Q: int, start_c: int):
        self.R0 = R0
        self.g = g
        self.Rfine = R0 + g
        self.Q = Q
        self.start = V(0, start_c % (3 ** self.Rfine))
        self._inv = {}

    def Mfine(self, j: int) -> int:
        return 3 ** (self.Rfine + j)

    def inv_pow2(self, t: int, j: int) -> int:
        key = (t, j)
        if key not in self._inv:
            M = self.Mfine(j)
            self._inv[key] = pow(pow(2, t, M), -1, M)
        return self._inv[key]

    def is_coarse_goal(self, v: V) -> bool:
        # projπ-image is an m-goal  ⇔  c ≡ 1 (mod 3^(R0+j))
        M = 3 ** (self.R0 + v.j)
        return v.c % M == 1 % M

    def is_fine_goal(self, v: V) -> bool:
        # (m+1)-goal  ⇔  c ≡ 1 (mod 3^(R0+g+j))
        M = 3 ** (self.Rfine + v.j)
        return v.c % M == 1 % M

    def outgoing(self, v: V):
        """(target, tau, is_zero_edge) for every admissible inverse edge."""
        out = []
        j, c = v.j, v.c
        M = self.Mfine(j)
        for a in ADMISSIBLE:
            t = TAU[a]
            y = (self.inv_pow2(t, j) * c) % M
            if y % 9 == a:
                out.append((V(j, y), t, False))
        if j < self.Q:
            M1 = self.Mfine(j + 1)
            val = (3 * c + 1) % M1
            for a in ADMISSIBLE:
                t = TAU[a]
                y = (self.inv_pow2(t, j + 1) * val) % M1
                if y % 9 == a:
                    out.append((V(j + 1, y), t, True))
        return out


# ----------------------------------------------------------------------------
# (L) Structural check: τ=1 and τ=3 zero-edges land on c ≡ 2 (mod 3),
#     hence break BOTH coarse and fine precision.
# ----------------------------------------------------------------------------
def check_tau1_breaks_precision(g: SynthGraph, max_states=40000):
    seen = {g.start}
    q = deque([g.start])
    viol = 0
    checked = 0
    while q and len(seen) < max_states:
        v = q.popleft()
        for (w, t, isz) in g.outgoing(v):
            if isz and t in (1, 3):
                checked += 1
                if w.c % 3 != 2:
                    viol += 1
                # c ≡ 2 mod 3  ⇒  not ≡ 1 mod 3^k for any k ≥ 1
                if g.is_coarse_goal(w) or g.is_fine_goal(w):
                    viol += 1
            if w not in seen:
                seen.add(w)
                q.append(w)
    return checked, viol, len(seen)


# ----------------------------------------------------------------------------
# Enumerate actual start→fine-goal paths (bounded), test the split claim.
# ----------------------------------------------------------------------------
def enumerate_paths_and_test(g: SynthGraph, max_len: int, max_paths: int):
    """DFS all simple-ish paths start→fine-goal up to max_len edges.

    For each path, compute mid = FIRST coarse-precision vertex strictly after
    start; the suffix mid→goal κ₂ = (#one − #τ1zero) on the suffix.
    Report the distribution of κ₂ and any path with NO valid split (κ₂≤0 for
    every coarse-precision interior split point).
    """
    results = {
        "paths": 0,
        "kappa2_first": {},          # κ₂ histogram for FIRST-coarse-point split
        "no_positive_split": 0,      # paths where NO coarse interior pt gives κ₂≥1
        "examples_bad": [],
        "examples_ok": [],
        "min_kappa2_best": None,     # min over paths of (best κ₂ achievable)
    }

    start = g.start

    # edge step weights for κ along the path
    def dfs(v, path_edges, depth):
        if results["paths"] >= max_paths:
            return
        if g.is_fine_goal(v) and depth > 0:
            results["paths"] += 1
            analyze_path(g, start, path_edges, results)
            # a fine goal is terminal for our purpose; continue exploring is
            # unnecessary and explosive, so stop here.
            return
        if depth >= max_len:
            return
        for (w, t, isz) in g.outgoing(v):
            # avoid trivial 2-cycles back to immediate predecessor vertex
            if path_edges and path_edges[-1][0] == w:
                continue
            dfs(w, path_edges + [(w, t, isz)], depth + 1)

    dfs(start, [], 0)
    return results


def analyze_path(g, start, path_edges, results):
    # vertices along path: start, then targets
    verts = [start] + [e[0] for e in path_edges]
    kap = [kappa_weight(e[1], e[2]) for e in path_edges]  # per-edge κ
    n = len(path_edges)

    # coarse-precision flags per vertex
    coarse = [g.is_coarse_goal(v) for v in verts]

    # FIRST coarse-precision index strictly after start (index >=1, < n  to keep
    # a non-empty suffix to the goal at index n)
    first_mid = None
    for i in range(1, n):           # interior only (exclude goal at i=n)
        if coarse[i]:
            first_mid = i
            break

    if first_mid is not None:
        suffix_k = sum(kap[first_mid:])   # κ₂ over edges first_mid..n-1
        results["kappa2_first"][suffix_k] = results["kappa2_first"].get(suffix_k, 0) + 1
    # best achievable κ₂ over ANY interior coarse split point
    best = None
    for i in range(1, n):
        if coarse[i]:
            sk = sum(kap[i:])
            best = sk if best is None else max(best, sk)
    if best is None:
        # no interior coarse point at all: split must be at goal ⇒ κ₂=0 only.
        # Does BlockBoundaryExists still hold? It needs κ₂≥1, so this path would
        # be a STRUCTURAL counterexample IF it is a real minimal path.
        results["no_positive_split"] += 1
        if len(results["examples_bad"]) < 6:
            results["examples_bad"].append({
                "verts": [(v.j, v.c) for v in verts],
                "kappa_edges": kap,
                "total_kappa": sum(kap),
                "reason": "no interior coarse-precision split point",
            })
        results["min_kappa2_best"] = 0 if results["min_kappa2_best"] is None \
            else min(results["min_kappa2_best"], 0)
        return

    if best <= 0:
        results["no_positive_split"] += 1
        if len(results["examples_bad"]) < 6:
            results["examples_bad"].append({
                "verts": [(v.j, v.c) for v in verts],
                "kappa_edges": kap,
                "coarse_flags": coarse,
                "best_suffix_kappa2": best,
            })
    else:
        if len(results["examples_ok"]) < 3:
            results["examples_ok"].append({
                "first_mid_idx": first_mid,
                "suffix_kappa2_firstmid": sum(kap[first_mid:]) if first_mid else None,
                "best_suffix_kappa2": best,
                "total_kappa": sum(kap),
                "len": n,
            })
    results["min_kappa2_best"] = best if results["min_kappa2_best"] is None \
        else min(results["min_kappa2_best"], best)


def run(R0, g_gap, Q, start_c, max_len, max_paths, label):
    G = SynthGraph(R0=R0, g=g_gap, Q=Q, start_c=start_c)
    print(f"=== {label}: R0={R0}, gap={g_gap} (Rfine={R0+g_gap}), Q={Q}, "
          f"start_c={G.start.c} ===")
    chk, viol, nseen = check_tau1_breaks_precision(G)
    print(f"  (L) τ∈{{1,3}} zero-edge targets checked: {chk}; "
          f"precision-break violations: {viol}  (region {nseen} states)")
    res = enumerate_paths_and_test(G, max_len=max_len, max_paths=max_paths)
    print(f"  start→fine-goal paths found (≤{max_len} edges): {res['paths']}")
    if res["paths"] == 0:
        print("  [no fine goals reachable in budget — increase max_len or "
              "lower gap]")
        return res
    print(f"  κ₂ histogram (FIRST coarse-precision split): "
          f"{dict(sorted(res['kappa2_first'].items()))}")
    print(f"  paths with NO κ₂≥1 interior split: {res['no_positive_split']}")
    print(f"  min over paths of BEST achievable κ₂: {res['min_kappa2_best']}")
    if res["examples_bad"]:
        print("  !! COUNTEREXAMPLE candidates (no positive split):")
        for ex in res["examples_bad"]:
            print("     ", ex)
    return res


if __name__ == "__main__":
    # Synthetic analogs. We pick small R0 and small gap so FINE goals (c≡1 to
    # full fine depth) are reachable in a short path, while the transition
    # structure is identical to the real graph.
    #
    # start_c = 1 + 3^R0  is the synthetic analog of aS202 = 1 + 3^22:
    #   it is coarse-NOT-precise? -> c-1 = 3^R0, ν₃ = R0, and coarse cap = R0,
    #   so c ≡ 1 mod 3^R0  -> actually coarse-PRECISE at j=0. To mirror aS202
    #   (which is coarse precise: δ₊(start)=22m-20>0 means NOT precise...).
    # aS202: c-1 = 3^22, ν₃(c-1)=22, coarse cap at level m is 22m+2.  For m=1
    #   cap=24 > 22, so ν₃ < cap  ⇒ NOT coarse-precise. Mirror: start_c-1=3^R0
    #   with coarse cap R0+? We want ν₃(start-1) < R0, so use start_c=1+3^(R0-1)
    #   (then ν₃=R0-1 < R0 at j=0, not coarse precise). Use that.
    for (R0, gap, Q) in [(3, 2, 4), (4, 2, 5), (3, 3, 6), (5, 2, 5)]:
        sc = 1 + 3 ** (R0 - 1)
        run(R0, gap, Q, sc, max_len=R0 + gap + Q + 8, max_paths=200000,
            label=f"synthetic m-analog")
        print()
