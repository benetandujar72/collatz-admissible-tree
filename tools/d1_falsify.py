"""
ANGLE D1 — FALSIFICATION sweep.  The make-or-break check.

We hunt for ANY (M, g, Q) on the faithful analog where the case-(b) floor K_b < M
(which would refute BOTH the barrier and the salvage), or where K_b < M+1 with the path
being case (b) (which refutes the salvage's "case (b) => kappa >= m+1" as a strict statement,
but NOT the barrier).

We push Q as high as tractable for the most adversarial small-g (g=2) regime, because tau=1
zero-edges (kappa=-1) are the only kappa-lowering move and a larger zero-budget Q allows more of
them.  If K_b stays == M as Q grows (never dipping below), the barrier floor is robust and TIGHT.

Outputs the min K_b over goals AND the second-smallest, to see the spectrum near the floor.
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
    adj = {}; seen = {start}; q = deque([start]); inc = False
    while q:
        if len(seen) > cap: inc = True; break
        s = q.popleft(); adj[s] = succ(s[0], s[1], B, Q)
        for (sp, ka) in adj[s]:
            if sp not in seen: seen.add(sp); q.append(sp)
    return B, start, adj, seen, inc

def spfa(start, adj, seen, blocked):
    INF = float('inf'); dist = {v: INF for v in seen}; dist[start] = 0
    dq = deque([start]); inq = {start}; cnt = {start: 0}; neg = False
    while dq:
        u = dq.popleft(); inq.discard(u)
        if u != start and blocked(u): continue
        du = dist[u]
        for (vv, ka) in adj.get(u, []):
            if du + ka < dist[vv]:
                dist[vv] = du + ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv] = cnt.get(vv, 0) + 1
                    if cnt[vv] > len(seen) + 1: neg = True; dq.clear(); break
    return dist, neg

def run(M, g, Q, cap=3_000_000):
    B, start, adj, seen, inc = build(M, g, Q, cap)
    R0 = B - g
    goal = lambda s: s[0] >= 1 and s[1] % 3 ** (B + s[0]) == 1 % 3 ** (B + s[0])
    mprec = lambda s: s[1] % 3 ** (R0 + s[0]) == 1 % 3 ** (R0 + s[0])
    goals = [v for v in seen if goal(v)]
    if not goals: return None
    d_all, n1 = spfa(start, adj, seen, lambda s: False)
    d_b, n2 = spfa(start, adj, seen, mprec)
    Kall = sorted(set(d_all[gg] for gg in goals))
    Kb = sorted(set(d_b[gg] for gg in goals))
    return {"B": B, "R0": R0, "inc": inc, "n": len(seen), "ngoal": len(goals),
            "Kall_spectrum": Kall[:6], "Kb_spectrum": Kb[:6],
            "Kall_min": Kall[0], "Kb_min": Kb[0], "neg": (n1 or n2)}

if __name__ == "__main__":
    print("FALSIFICATION sweep: hunting K_b < M (would break barrier) on faithful analog.\n")
    worst = []
    plan = [
        (2, 2, range(1, 11)),
        (2, 3, range(1, 6)),
        (2, 4, range(1, 4)),
        (3, 2, range(1, 6)),
        (4, 2, range(1, 4)),
        (5, 2, range(1, 3)),
    ]
    for (M, g, Qs) in plan:
        for Q in Qs:
            r = run(M, g, Q)
            if r is None:
                continue
            flag = ""
            if r["Kb_min"] < M: flag = "  <<< BARRIER VIOLATED (K_b<M)"
            elif r["Kb_min"] == M: flag = "  [floor==M, tight]"
            inc = " INC" if r["inc"] else ""
            print(f"M={M} g={g} Q={Q}: st={r['n']:>8}{inc} ngoal={r['ngoal']:>3} "
                  f"K_all_min={r['Kall_min']} K_b_min={r['Kb_min']} "
                  f"Kb_spec={r['Kb_spectrum']}{flag}")
            worst.append((M, g, Q, r["Kb_min"], r["Kb_min"] - M))
        print()
    print("Summary: min over all (K_b - M):", min(x[4] for x in worst),
          "(>=0 means barrier floor held everywhere)")
    bad = [x for x in worst if x[3] < x[0]]
    print("Cases with K_b < M:", bad if bad else "NONE — barrier floor K_b>=M held in every case.")
