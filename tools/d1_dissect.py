"""
ANGLE D1 — dissect the K_b == M anomaly at small gap g, and measure how K_b scales with g.

For the decisive cases we:
  (1) reconstruct the actual MIN-kappa case-(b) path (no M-precise interior) and print its edge trace
      (kappa per edge, dlog at working & coarse level, mod-9 class), to SEE whether it uses the deep
      jump and how it achieves kappa as low as it does;
  (2) tabulate K_b(g) and K_all(g) for fixed M=2 across increasing Q (saturating) to extract the
      LIMITING floor as Q->inf, and how that limit grows with g.

The real problem is g=22 (LARGE). The question: does K_b -> (something >= M+1) as g grows, or does the
g=2 phenomenon K_b==M persist? We extract the trend.
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
        if cp % 9 == a: out.append(((j, cp), +1, 'one', t))
    if j < Q:
        M1 = 3 ** (B + j + 1); val = (3 * c + 1) % M1
        for a in ADMISSIBLE:
            t = TAU[a]; cp = (inv2pow(t, M1) * val) % M1
            if cp % 9 == a: out.append(((j + 1, cp), -1 if t == 1 else 0, 'zero', t))
    return out

def build(M, g, Q, cap):
    B = g * M + 2; start = (0, (1 + 3 ** g) % 3 ** B)
    adj = {}; seen = {start}; q = deque([start]); inc = False
    while q:
        if len(seen) > cap: inc = True; break
        s = q.popleft(); adj[s] = [(sp, ka) for (sp, ka, kd, t) in succ(s[0], s[1], B, Q)]
        for (sp, ka) in adj[s]:
            if sp not in seen: seen.add(sp); q.append(sp)
    return B, start, adj, seen, inc

def spfa_pred(start, adj, seen, blocked):
    INF = float('inf'); dist = {v: INF for v in seen}; dist[start] = 0
    pred = {start: None}
    dq = deque([start]); inq = {start}; cnt = {start: 0}
    while dq:
        u = dq.popleft(); inq.discard(u)
        if u != start and blocked(u): continue
        du = dist[u]
        for (vv, ka) in adj.get(u, []):
            if du + ka < dist[vv]:
                dist[vv] = du + ka; pred[vv] = (u, ka)
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv] = cnt.get(vv, 0) + 1
                    if cnt[vv] > len(seen) + 1: dq.clear(); break
    return dist, pred

# fast dlog at level k for a unit residue (Pohlig-Hellman, O(k^2))
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
def dlog_at(c, k):
    return fast_dlog(c % 3 ** k, k)

def trace_path(M, g, Q, cap=2_500_000):
    B, start, adj, seen, inc = build(M, g, Q, cap)
    R0 = B - g
    goal = lambda s: s[0] >= 1 and s[1] % 3 ** (B + s[0]) == 1 % 3 ** (B + s[0])
    mprec = lambda s: s[1] % 3 ** (R0 + s[0]) == 1 % 3 ** (R0 + s[0])
    goals = [v for v in seen if goal(v)]
    dist, pred = spfa_pred(start, adj, seen, mprec)
    # pick the goal achieving the min K_b
    gg = min(goals, key=lambda v: dist[v])
    Kb = dist[gg]
    # reconstruct
    path = []; cur = gg
    while cur is not None:
        path.append(cur); nxt = pred.get(cur)
        cur = nxt[0] if nxt is not None else None
    path.reverse()
    print(f"--- M={M} g={g} Q={Q}: B={B} R0={R0}  K_b={Kb}  (path length {len(path)-1} edges) ---")
    for i, v in enumerate(path):
        j, c = v
        wk = B + j; ck = R0 + j
        wdl = dlog_at(c, wk); cdl = dlog_at(c % 3 ** ck, ck)
        tag = []
        if mprec(v): tag.append("M-PRECISE")
        if goal(v): tag.append("GOAL")
        edge = ""
        if i > 0:
            pv = pred[v]  # (u, ka)
            edge = f"  <kappa={pv[1]:+d}>"
        print(f"   [{i}] j={j} c={c} (c%9={c%9}) work_dlog={wdl} coarse_dlog={cdl}{edge}  {' '.join(tag)}")
    return Kb

def scale_table(M, g, Qs, cap=2_500_000):
    B0 = g * M + 2
    print(f"=== K_b / K_all scaling, M={M}, g={g} (B={B0}, R0={B0-g}) ===")
    prev = None
    for Q in Qs:
        Bc, start, adj, seen, inc = build(M, g, Q, cap)
        R0 = Bc - g
        goal = lambda s: s[0] >= 1 and s[1] % 3 ** (Bc + s[0]) == 1 % 3 ** (Bc + s[0])
        mprec = lambda s: s[1] % 3 ** (R0 + s[0]) == 1 % 3 ** (R0 + s[0])
        goals = [v for v in seen if goal(v)]
        if not goals:
            print(f"  Q={Q}: no goal"); continue
        d_all, _ = spfa_pred(start, adj, seen, lambda s: False)
        d_b, _ = spfa_pred(start, adj, seen, mprec)
        Kall = min(d_all[gg] for gg in goals); Kb = min(d_b[gg] for gg in goals)
        inc_t = " [INC]" if inc else ""
        print(f"  Q={Q}: st={len(seen):>8}{inc_t} goals={len(goals)} K_all={Kall} K_b={Kb}")

if __name__ == "__main__":
    print("PART A — trace the MIN-kappa case-(b) path at the K_b==M anomaly (M=2,g=2,Q=4):\n")
    trace_path(2, 2, 4)
    print()
    print("PART B — also trace a LARGER-gap case (M=2,g=3,Q=4) where K_b was 19:\n")
    trace_path(2, 3, 4)
    print()
    print("PART C — how does K_b scale with g (saturating Q)?  M=2.\n")
    for g in [2, 3, 4]:
        scale_table(2, g, list(range(1, 9)))
        print()
