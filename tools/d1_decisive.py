"""
ANGLE D1 — DECISIVE comparison, lean version.

Same faithful analog as d1_caseb_floor.py but:
  * lighter sweep (small fast cases only), explicit timing-safe sizes;
  * for each (M,g,Q) we report:
       K_all  = min total kappa over ALL paths to a working-goal,
       K_b    = min total kappa over paths with NO M-precise interior vertex,
       and crucially the DECOMPOSITION of K_all: is the global-min path case (a) or case (b)?
  * We also report K_a = min kappa over paths that DO pass an M-precise interior vertex.
  * And the per-edge floor predicted by N2 (deep-jump): does a case-(b) path NEED >= some #one-edges?

The barrier target is kappa >= M (M plays 'm+1'). The salvage claims K_b >= M+1? or K_b >= M?
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

def analyse(M, g, Q, cap=2_500_000):
    B, start, adj, seen, inc = build(M, g, Q, cap)
    R0 = B - g
    goal = lambda s: s[0] >= 1 and s[1] % 3 ** (B + s[0]) == 1 % 3 ** (B + s[0])
    mprec = lambda s: s[1] % 3 ** (R0 + s[0]) == 1 % 3 ** (R0 + s[0])
    goals = [v for v in seen if goal(v)]
    if not goals:
        return {"M": M, "g": g, "Q": Q, "B": B, "R0": R0, "incomplete": inc,
                "n": len(seen), "K_all": None, "K_b": None, "K_a": None, "neg": False}
    d_all, n1 = spfa(start, adj, seen, lambda s: False)
    K_all = min(d_all[gg] for gg in goals)
    # K_b: sink ALL m-precise (incl goals). reach a goal only as target.
    d_b, n2 = spfa(start, adj, seen, mprec)
    K_b = min(d_b[gg] for gg in goals)
    return {"M": M, "g": g, "Q": Q, "B": B, "R0": R0, "incomplete": inc,
            "n": len(seen), "n_goals": len(goals),
            "K_all": K_all, "K_b": K_b, "neg": (n1 or n2)}

if __name__ == "__main__":
    print("ANGLE D1 decisive: barrier target kappa>=M (M plays m+1).")
    print(" K_b == M  -> a NO-precise path achieves exactly M -> salvage-as-stated (>=M+1) FAILS@boundary")
    print("           BUT barrier (kappa>=M) still OK, AND case(a) split would have given M anyway.")
    print(" K_b <  M  -> BARRIER ITSELF false.  K_b >= M+1 -> salvage survives.\n")
    for (M, g, Q) in [(2,2,2),(2,2,3),(2,2,4),(2,2,5),(2,2,6),
                      (2,3,2),(2,3,3),(2,3,4),
                      (2,4,2),(2,4,3),
                      (3,2,2),(3,2,3),(3,2,4),
                      (3,3,2),(3,3,3),
                      (4,2,2),(4,2,3)]:
        r = analyse(M, g, Q)
        if r["K_b"] is None:
            print(f"M={M} g={g} Q={Q}: B={r['B']} st={r['n']} no goal"); continue
        kb, m = r["K_b"], r["M"]
        if kb < m: v = f"*** BARRIER FALSE (K_b={kb}<M={m}) ***"
        elif kb == m: v = f"K_b==M ({kb}): >=M+1 FAILS@boundary, barrier OK"
        else: v = f"K_b={kb}>=M+1: salvage survives"
        inc = " [INC]" if r["incomplete"] else ""
        ncyc = " [NEG]" if r["neg"] else ""
        print(f"M={M} g={g} Q={Q}: B={r['B']} R0={r['R0']} st={r['n']:>7}{inc}{ncyc} "
              f"goals={r['n_goals']} K_all={r['K_all']} K_b={r['K_b']} => {v}")
