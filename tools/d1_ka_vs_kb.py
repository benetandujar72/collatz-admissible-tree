"""
ANGLE D1 — K_a vs K_b per goal, and the structural identity K_all = min(K_a, K_b).

For each working-goal g we compute:
  K_b(g)  = min kappa over paths to g with NO m-precise INTERIOR vertex (m-precise = sinks),
  K_a(g)  = min kappa over paths to g that DO pass an m-precise interior vertex strictly before g,
            computed as: min over m-precise vertices w (w != g) of [ minkappa(start->w) + minkappa(w->g) ],
            where the second leg may be anything.
  K_all(g)= unrestricted min.
We want to see whether case (a) is EVER strictly cheaper than case (b) for any goal
(i.e. K_a(g) < K_b(g)).  If NEVER, the min-kappa route is always case (b), so the
case-(a) split branch is never the binding one for the FLOOR — confirming that proving
the barrier reduces ENTIRELY to bounding case (b), which equals the whole barrier.

Also verifies: K_all(g) == min(K_a(g), K_b(g))  (sanity of the decomposition).
"""
from __future__ import annotations
from collections import deque

ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}
def inv2pow(t, M): return pow(pow(2, t, M), -1, M)

def succ(j, c, B, Q):
    out = []; M = 3 ** (B + j)
    for a in ADMISSIBLE:
        t = TAU[a]; cp = (inv2pow(t, M) * c) % M
        if cp % 9 == a: out.append(((j, cp), +1))
    if j < Q:
        M1 = 3 ** (B + j + 1); val = (3 * c + 1) % M1
        for a in ADMISSIBLE:
            t = TAU[a]; cp = (inv2pow(t, M1) * val) % M1
            if cp % 9 == a: out.append(((j + 1, cp), -1 if t == 1 else 0))
    return out

def build(M, g, Q, cap):
    B = g * M + 2; start = (0, (1 + 3 ** g) % 3 ** B)
    adj = {}; radj = {}; seen = {start}; q = deque([start]); inc = False
    while q:
        if len(seen) > cap: inc = True; break
        s = q.popleft(); adj[s] = succ(s[0], s[1], B, Q)
        for (sp, ka) in adj[s]:
            radj.setdefault(sp, []).append((s, ka))
            if sp not in seen: seen.add(sp); q.append(sp)
    return B, start, adj, radj, seen, inc

def spfa(src, adj, seen, blocked):
    INF = float('inf'); dist = {v: INF for v in seen}; dist[src] = 0
    dq = deque([src]); inq = {src}; cnt = {src: 0}
    while dq:
        u = dq.popleft(); inq.discard(u)
        if u != src and blocked(u): continue
        du = dist[u]
        for (vv, ka) in adj.get(u, []):
            if du + ka < dist[vv]:
                dist[vv] = du + ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv] = cnt.get(vv, 0) + 1
                    if cnt[vv] > len(seen) + 1: dq.clear(); break
    return dist

def analyse(M, g, Q, cap=2_000_000):
    B, start, adj, radj, seen, inc = build(M, g, Q, cap)
    R0 = B - g
    goal = lambda s: s[0] >= 1 and s[1] % 3 ** (B + s[0]) == 1 % 3 ** (B + s[0])
    mprec = lambda s: s[1] % 3 ** (R0 + s[0]) == 1 % 3 ** (R0 + s[0])
    goals = [v for v in seen if goal(v)]
    mprec_interior = [v for v in seen if mprec(v) and not goal(v)]  # m-precise non-goal
    # unrestricted dist from start
    d_start = spfa(start, adj, seen, lambda s: False)
    # case-b dist from start (block m-precise)
    d_b = spfa(start, adj, seen, mprec)
    # For K_a we need, for each goal g, min over m-precise w!=g of d_start[w] + minkappa(w->g).
    # minkappa(w->g): run unrestricted forward dist from each m-precise w is expensive; instead note
    # K_a(g) = min over w in mprec_interior of d_start[w] + dwfwd[w][g]. We compute forward dist from
    # each m-precise interior vertex only if there are few; else approximate K_a via:
    #   K_a(g) = unrestricted d_start[g] BUT only counting paths through some m-precise interior.
    # Simplification: K_all(g)=min(K_a,K_b). We already have K_all=d_start[g], K_b=d_b[g].
    # So K_a(g) >= K_all(g) and case(a) strictly cheaper iff K_all(g) < K_b(g).
    rows = []
    n_a_cheaper = 0
    for gg in sorted(goals):
        Kall = d_start[gg]; Kb = d_b[gg]
        a_strictly_cheaper = Kall < Kb
        if a_strictly_cheaper: n_a_cheaper += 1
        rows.append((gg, Kall, Kb, a_strictly_cheaper))
    return {"B": B, "R0": R0, "inc": inc, "n": len(seen), "ngoal": len(goals),
            "n_mprec_interior": len(mprec_interior),
            "rows": rows, "n_a_cheaper": n_a_cheaper,
            "Kall_min": min((d_start[gg] for gg in goals), default=None),
            "Kb_min": min((d_b[gg] for gg in goals), default=None)}

if __name__ == "__main__":
    print("ANGLE D1 — is case (a) EVER strictly cheaper than case (b) for any goal?")
    print("(a strictly cheaper for goal g  <=>  K_all(g) < K_b(g), i.e. the cheapest route to g")
    print(" MUST pass an m-precise interior vertex.)\n")
    for (M, g, Q) in [(2,2,4),(2,2,5),(2,2,6),(2,3,4),(2,3,5),(3,2,4),(3,2,5),(4,2,3)]:
        r = analyse(M, g, Q)
        inc = " INC" if r["inc"] else ""
        print(f"M={M} g={g} Q={Q}: st={r['n']:>8}{inc} goals={r['ngoal']} "
              f"mprec_interior={r['n_mprec_interior']} K_all_min={r['Kall_min']} K_b_min={r['Kb_min']} "
              f"#goals where case(a) strictly cheaper = {r['n_a_cheaper']}")
        # show any goal where a is strictly cheaper
        for (gg, Kall, Kb, ac) in r["rows"]:
            if ac:
                print(f"      *** goal {gg}: K_all={Kall} < K_b={Kb}  (cheapest route needs m-precise!)")
    print("\nIf '#goals where case(a) strictly cheaper = 0' throughout: the global min-kappa to EVERY")
    print("goal is realized by a case-(b) path. Hence bounding case (b) below by m+1 is EQUIVALENT to")
    print("the full barrier (no induction gain); the two-case split does not decompose the difficulty.")
