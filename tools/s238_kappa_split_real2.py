"""
s238_kappa_split_real2.py — POSITIVE-side test on the REAL S202 graph.

Real-graph finding (s238_kappa_split_real.py): a SINGLE one-edge reaches ρ₊
(=ν₃(c−1)) at most ~10 in the cost-bounded region, FAR below a 22-digit gap.
So fine precision cannot be reached by one edge skipping the coarse threshold;
it must be built GRADUALLY. If so, the coarse threshold (cap Kc) is crossed by
an EARLIER edge than the fine threshold (cap Kc+gap), giving a genuine interior
coarse-precision split point — and we then measure the suffix κ₂.

Because true (m+1)-goals are astronomically deep, we instead pick a SMALL fine
cap Kf reachable in the real graph (so genuine "fine goals" exist), with coarse
cap Kc = Kf − gap. We Dijkstra (SPFA, κ-cost) from the REAL start to all real
vertices, find those that are fine-precise (ρ₊(c, Kf+j) = Kf+j), reconstruct a
min-κ path, and check: (a) does an interior coarse-precise vertex exist?
(b) suffix κ₂ from the FIRST one ≥ 1?

This keeps the genuine S202 transition structure AND a real ≥1 multi-digit gap,
while staying computationally tractable (small Kf).
"""
from __future__ import annotations
from collections import deque
from s202_engine import S202Engine, State, ADMISSIBLE, TAU


def nu3(x: int) -> int:
    if x == 0:
        return 10**9
    x = abs(x)
    k = 0
    while x % 3 == 0:
        x //= 3
        k += 1
    return k


def kappa(t, isz):
    if not isz:
        return 1
    return -1 if t == 1 else 0


def edges_with_class(eng: S202Engine, s: State):
    """Real engine edges, tagged (target, tau, is_zero)."""
    out = []
    j, c = s.j, s.c
    M = eng.modulus(j)
    for a in ADMISSIBLE:
        t = TAU[a]
        y = (eng.inv_pow2(t, j) * c) % M
        if y % 9 == a:
            out.append((State(j, y), t, False))
    if j < eng.Q:
        M1 = eng.modulus(j + 1)
        val = (3 * c + 1) % M1
        for a in ADMISSIBLE:
            t = TAU[a]
            y = (eng.inv_pow2(t, j + 1) * val) % M1
            if y % 9 == a:
                out.append((State(j + 1, y), t, True))
    return out


def run(m, Q, Kf, gap, max_states=400000):
    eng = S202Engine(m=m, Q=Q)
    Kc = Kf - gap
    assert Kc >= 1
    start = eng.start

    def is_fine(v):
        cap = Kf + v.j
        return min(nu3(v.c - 1), cap) == cap

    def coarse_def(v):
        cap = Kc + v.j
        return cap - min(nu3(v.c - 1), cap)

    # SPFA over κ-cost (edges can be negative) from start.
    dist = {start: 0}
    pred = {start: None}
    inq = {start}
    q = deque([start])
    goals = set()
    while q and len(dist) <= max_states:
        v = q.popleft(); inq.discard(v)
        d = dist[v]
        if is_fine(v) and v != start:
            goals.add(v)
            continue
        for (w, t, isz) in edges_with_class(eng, v):
            nd = d + kappa(t, isz)
            if w not in dist or nd < dist[w]:
                dist[w] = nd
                pred[w] = (v, t, isz)
                if w not in inq:
                    q.append(w); inq.add(w)

    def reconstruct(go):
        verts = []; edges = []
        cur = go
        while cur is not None:
            verts.append(cur)
            p = pred.get(cur)
            if p is None:
                break
            pv, t, isz = p
            edges.append((t, isz)); cur = pv
        verts.reverse(); edges.reverse()
        return verts, edges

    n_interior = 0; n_only_goal = 0
    suffix_hist = {}
    bad = []
    for go in goals:
        verts, edges = reconstruct(go)
        if not edges:
            continue
        kap = [kappa(t, isz) for (t, isz) in edges]
        n = len(edges)
        cdef = [coarse_def(v) for v in verts]
        coarse = [x == 0 for x in cdef]
        first_mid = next((i for i in range(1, n) if coarse[i]), None)
        if first_mid is not None:
            n_interior += 1
            sk = sum(kap[first_mid:])
            suffix_hist[sk] = suffix_hist.get(sk, 0) + 1
            if sk <= 0 and len(bad) < 6:
                bad.append(("interior κ2<=0", n, sum(kap), cdef))
        else:
            n_only_goal += 1
            if len(bad) < 6:
                bad.append(("ONLY-goal-coarse", n, sum(kap), cdef))
    print(f"=== REAL m={m} Q={Q} | Kf={Kf} Kc={Kc} gap={gap} | "
          f"states={len(dist)} fine-goals={len(goals)} ===")
    print(f"   interior-coarse-point paths={n_interior}, "
          f"ONLY-goal-coarse paths={n_only_goal}")
    print(f"   suffix κ₂ histogram (first interior coarse split): "
          f"{dict(sorted(suffix_hist.items()))}")
    if bad:
        print("   danger/sample paths:")
        for tag, ln, tk, cdef in bad:
            print(f"     [{tag}] len={ln} totalκ={tk} coarse_def_seq={cdef}")
    print()


if __name__ == "__main__":
    # Keep Kf small so fine goals are reachable in the real graph. Sweep gap.
    for (Kf, gap) in [(3, 1), (3, 2), (4, 2), (4, 3), (5, 3), (5, 4), (6, 4)]:
        run(m=1, Q=14, Kf=Kf, gap=gap)
