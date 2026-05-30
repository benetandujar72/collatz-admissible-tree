"""
s238_kappa_split_probe2.py — sharpened TRUTH PROBE for BlockBoundaryExists.

Probe1 finding: in the synthetic analog, start→fine-goal paths typically reach
COARSE precision only AT the goal (the c-values collapse to 1 in the last few
one-edges), so the only split point is trivial (κ₂=0). That is itself a danger
signal, but it could be an artifact of a tiny coarse/fine gap (coarse and fine
achieved together).

This sharpened probe:
  (1) tracks the COARSE deficit  δ_c(v) = (R0+j) − min(ν₃(c−1), R0+j)  along
      every path, and records the index of the FIRST coarse-precision vertex
      (δ_c = 0) strictly before the goal — to see whether a NONTRIVIAL split
      point exists at all;
  (2) for paths that DO have an interior coarse-precision point, reports the
      suffix κ₂ from the FIRST such point to the fine goal;
  (3) uses Dijkstra on κ-cost to find, for each reachable fine goal, a MINIMUM-κ
      witness path (the adversary's best attempt to make κ₂ small);
  (4) sweeps the coarse/fine gap to test whether "coarse achieved only at goal"
      persists as the gap grows (faithful to the real 22-digit gap) or is a
      small-gap artifact.

Interpretation key:
  • If, as gap grows, paths reliably acquire an interior coarse-precision point
    with suffix κ₂ ≥ 1  ⇒  BlockBoundaryExists is plausibly TRUE.
  • If there persist minimal paths whose ONLY coarse-precision point is the goal
    (κ₂ forced = 0)  ⇒  BlockBoundaryExists is in jeopardy (the split is trivial,
    the R1 trap reappears uniformly).
"""
from __future__ import annotations
from collections import deque
import heapq
from dataclasses import dataclass
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


def kappa_weight(t: int, isz: bool) -> int:
    if not isz:
        return 1
    return -1 if t == 1 else 0


@dataclass(frozen=True)
class V:
    j: int
    c: int


class G:
    def __init__(self, R0, gap, Q, start_c):
        self.R0, self.gap, self.Q = R0, gap, Q
        self.Rfine = R0 + gap
        self.start = V(0, start_c % 3 ** self.Rfine)
        self._inv = {}

    def M(self, j):
        return 3 ** (self.Rfine + j)

    def inv2(self, t, j):
        k = (t, j)
        if k not in self._inv:
            m = self.M(j)
            self._inv[k] = pow(pow(2, t, m), -1, m)
        return self._inv[k]

    def coarse_def(self, v):
        cap = self.R0 + v.j
        return cap - min(nu3(v.c - 1), cap)

    def is_coarse(self, v):
        return self.coarse_def(v) == 0

    def is_fine(self, v):
        cap = self.Rfine + v.j
        return v.c % (3 ** cap) == 1 % (3 ** cap)

    def out(self, v):
        o = []
        j, c = v.j, v.c
        m = self.M(j)
        for a in ADMISSIBLE:
            t = TAU[a]
            y = (self.inv2(t, j) * c) % m
            if y % 9 == a:
                o.append((V(j, y), t, False))
        if j < self.Q:
            m1 = self.M(j + 1)
            val = (3 * c + 1) % m1
            for a in ADMISSIBLE:
                t = TAU[a]
                y = (self.inv2(t, j + 1) * val) % m1
                if y % 9 == a:
                    o.append((V(j + 1, y), t, True))
        return o


def dijkstra_min_kappa_to_goals(g: G, max_states=200000):
    """Min κ-cost from start to every reachable vertex, with predecessor +
    incoming-edge record, so we can reconstruct a min-κ path to any fine goal.
    κ can be negative (τ=1 zeros), but along admissible paths the suffix bound
    keeps things finite within the bounded slice; we cap states for safety.
    Because of possible negative edges we use Bellman-Ford-ish relaxation via a
    queue (SPFA)."""
    INF = 10**18
    dist = {g.start: 0}
    pred = {g.start: None}        # vertex -> (prev_vertex, tau, isz)
    inq = {g.start}
    q = deque([g.start])
    goals = set()
    while q:
        v = q.popleft()
        inq.discard(v)
        d = dist[v]
        if g.is_fine(v) and v != g.start:
            goals.add(v)
            # goal is terminal — do not expand further (mirrors barrier search)
            continue
        if len(dist) > max_states:
            break
        for (w, t, isz) in g.out(v):
            nd = d + kappa_weight(t, isz)
            if w not in dist or nd < dist[w]:
                dist[w] = nd
                pred[w] = (v, t, isz)
                if w not in inq:
                    q.append(w)
                    inq.add(w)
    return dist, pred, goals


def reconstruct(pred, goal):
    """Return list of vertices start..goal and list of (tau,isz) edges."""
    verts = []
    edges = []
    cur = goal
    while cur is not None:
        verts.append(cur)
        p = pred.get(cur)
        if p is None:
            break
        pv, t, isz = p
        edges.append((t, isz))
        cur = pv
    verts.reverse()
    edges.reverse()
    return verts, edges


def analyze(g: G, verts, edges):
    kap = [kappa_weight(t, isz) for (t, isz) in edges]
    n = len(edges)
    coarse = [g.is_coarse(v) for v in verts]      # length n+1
    cdef = [g.coarse_def(v) for v in verts]
    # first interior coarse-precision index (1..n-1); n is the goal
    first_mid = next((i for i in range(1, n) if coarse[i]), None)
    info = {
        "len": n,
        "total_kappa": sum(kap),
        "first_mid_idx": first_mid,
        "suffix_kappa2": (sum(kap[first_mid:]) if first_mid is not None else None),
        "coarse_def_seq": cdef,
        "has_interior_coarse": first_mid is not None,
    }
    return info


def run(R0, gap, Q, start_c, label):
    g = G(R0, gap, Q, start_c)
    dist, pred, goals = dijkstra_min_kappa_to_goals(g)
    print(f"=== {label}: R0={R0} gap={gap} Q={Q} start_c={g.start.c} "
          f"| reachable fine-goals: {len(goals)} ===")
    if not goals:
        print("   no fine goals reachable — skip")
        return
    n_interior = 0
    n_trivial_only = 0
    bad = []
    suffixk = {}
    for go in goals:
        verts, edges = reconstruct(pred, go)
        if not edges:
            continue
        info = analyze(g, verts, edges)
        if info["has_interior_coarse"]:
            n_interior += 1
            sk = info["suffix_kappa2"]
            suffixk[sk] = suffixk.get(sk, 0) + 1
            if sk is not None and sk <= 0:
                bad.append(("interior but κ2<=0", info, [(v.j, v.c) for v in verts]))
        else:
            n_trivial_only += 1
            if len(bad) < 8:
                bad.append(("ONLY-goal-coarse (κ2 forced 0)", info,
                            [(v.j, v.c) for v in verts]))
    print(f"   min-κ goal paths: interior-coarse-point={n_interior}, "
          f"ONLY-goal-coarse={n_trivial_only}")
    print(f"   suffix κ₂ histogram (first interior coarse split): "
          f"{dict(sorted((k, v) for k, v in suffixk.items() if k is not None))}")
    if bad:
        print(f"   danger paths ({len(bad)} shown up to 8):")
        for tag, info, vv in bad[:8]:
            print(f"      [{tag}] len={info['len']} totalκ={info['total_kappa']} "
                  f"coarse_def_seq={info['coarse_def_seq']}")
    print()


if __name__ == "__main__":
    # Gap sweep at fixed coarse base R0=3, faithful start_c = 1 + 3^(R0-1)
    # (ν₃(start-1)=R0-1 < R0  ⇒ start NOT coarse-precise, mirroring aS202).
    print("########## GAP SWEEP (coarse base R0=3) ##########\n")
    for gap in [1, 2, 3, 4, 5]:
        run(R0=3, gap=gap, Q=4 + gap, start_c=1 + 3 ** 2,
            label=f"gap-sweep")
    # Different coarse bases
    print("########## VARYING COARSE BASE ##########\n")
    for (R0, gap, Q) in [(2, 4, 6), (4, 3, 7), (2, 6, 8), (5, 3, 7)]:
        run(R0=R0, gap=gap, Q=Q, start_c=1 + 3 ** (R0 - 1),
            label="vary-base")
