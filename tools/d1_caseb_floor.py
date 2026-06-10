"""
ANGLE D1 — the case-(b) kappa-floor.

Setup (FAITHFUL scaled analog of the (m+1)-cylinder barrier).
  * Cylinder index M (plays the role of "m+1"). Run from InvStart(M).
  * Working level B = 22*M + 2  (the goal precision; goal: c ≡ 1 mod 3^(B+j)).
  * The m-precise / "shadow-goal" level is the COARSER R0 = 22*(M-1) + 2,
    i.e. a vertex (j,c) is M-PRECISE  iff  c ≡ 1 mod 3^(R0+j).
    (This is the analog of projMPrecise: project down by one 22-block.)
  * The 22-digit FREE FIBRE between R0 and B is exactly reproduced (B - R0 = 22).

kappa edges:  one-edge +1 ; tau=1 zero -1 ; tau>=2 zero 0.

THE TWO-CASE SALVAGE (ANGLE D1) asks: does every M-goal-path satisfy kappa >= M, with
  (a) an M-precise intermediate strictly before the goal  -> split, IH gives kappa1>=M-1, suffix +1; OR
  (b) NO M-precise intermediate  -> N2 forces a long ladder, so kappa >= M directly?

We compute THREE Bellman-Ford minima over the EXACT finite reachable graph:
  K_all  := min total kappa over ALL paths InvStart(M) -> working-goal           (the BARRIER metric)
  K_b    := min total kappa over paths whose INTERIOR avoids every M-precise vertex (case (b) floor)
            [M-precise vertices are made SINKS: you may END at the goal (itself M-precise) but never
             pass THROUGH an M-precise interior vertex]
  K_a    := min total kappa over paths that DO hit an M-precise interior vertex strictly before goal.

DECISION:
  * If  K_b >= M+1  : case (b) really has floor >= "m+1", the two-case salvage SURVIVES at this scale.
  * If  K_b == M    : case (b) floor is only M (=" m+1" would need >= M+1) -> the SALVAGE-as-stated
                      FAILS at the boundary (a no-precise path achieves exactly M, not M+1).
  * If  K_b <  M    : the BARRIER ITSELF is false at this scale (a no-precise path beats M).

Faithful index: M plays "m+1", so the IH level is M-1; "m+1 >= ..." in the prompt is "M" here.
Tractable for M=2 (B=6 in the analog with 22->2 rescaling? NO — we keep the TRUE 22 gap only in the
forbidden level via R0=22(M-1)+2 vs B=22M+2). To stay tractable we use the SCALED gap g (g plays 22):
B = g*M + 2, R0 = g*(M-1)+2, so B-R0 = g. We sweep g in {2,3,4} and M in {2,3} and watch the verdict.
"""
from __future__ import annotations
from collections import deque

ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}

def inv2pow(t, M): return pow(pow(2, t, M), -1, M)

def succ(j, c, B, Q):
    """Inverse-graph successors at natural precision. Returns ((j',c'), kappa)."""
    out = []
    M = 3 ** (B + j)
    for a in ADMISSIBLE:
        t = TAU[a]; cp = (inv2pow(t, M) * c) % M
        if cp % 9 == a:
            out.append(((j, cp), +1))
    if j < Q:
        M1 = 3 ** (B + j + 1); val = (3 * c + 1) % M1
        for a in ADMISSIBLE:
            t = TAU[a]; cp = (inv2pow(t, M1) * val) % M1
            if cp % 9 == a:
                out.append(((j + 1, cp), -1 if t == 1 else 0))
    return out

def aS202_analog(g):
    # start residue analog: 1 + 3^g  (so it is NOT 1 at the R0 level, like aS202=1+3^22)
    return 1 + 3 ** g

def build_graph(M, g, Q, max_states):
    B = g * M + 2
    start = (0, aS202_analog(g) % 3 ** B)
    adj = {}; seen = {start}; q = deque([start]); inc = False
    while q:
        if len(seen) > max_states:
            inc = True; break
        s = q.popleft(); adj[s] = succ(s[0], s[1], B, Q)
        for (sp, ka) in adj[s]:
            if sp not in seen:
                seen.add(sp); q.append(sp)
    return B, start, adj, seen, inc

def is_goal(s, B):       # working goal
    j, c = s; return c % 3 ** (B + j) == 1 % 3 ** (B + j)
def is_mprecise(s, B, g):  # M-precise = shadow goal at the coarser R0 level
    j, c = s; R0 = B - g; return c % 3 ** (R0 + j) == 1 % 3 ** (R0 + j)

def spfa(start, adj, seen, blocked=lambda s: False):
    """Min total kappa from start. 'blocked' vertices are SINKS: edges OUT of them are dropped
    (so a path may END at a blocked vertex but never continue through it)."""
    INF = float('inf'); dist = {v: INF for v in seen}; dist[start] = 0
    dq = deque([start]); inq = {start}; cnt = {start: 0}; neg = False
    while dq:
        u = dq.popleft(); inq.discard(u)
        if blocked(u) and u != start:
            continue
        du = dist[u]
        for (vv, ka) in adj.get(u, []):
            if du + ka < dist.get(vv, INF):
                dist[vv] = du + ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv] = cnt.get(vv, 0) + 1
                    if cnt[vv] > len(seen) + 1:
                        neg = True; dq.clear(); break
    return dist, neg

def analyse(M, g, Q, max_states=4_000_000):
    B, start, adj, seen, inc = build_graph(M, g, Q, max_states)
    goals = [v for v in seen if is_goal(v, B) and v[0] >= 1]
    # K_all : unrestricted
    dist_all, neg1 = spfa(start, adj, seen)
    K_all = min((dist_all[gg] for gg in goals), default=None)
    # K_b : block (make sinks) every M-precise vertex EXCEPT we still allow ending AT the goal.
    #   Implementation: the goal is itself M-precise; to allow reaching it we must NOT sink it
    #   prematurely. But a goal has no need to be expanded further to be 'reached'. So we sink
    #   ALL M-precise vertices including goals; the goal is reached as a TARGET (incoming edge),
    #   its outgoing edges are irrelevant for the min-to-goal. This exactly encodes "no M-precise
    #   INTERIOR vertex": any path whose interior hit an M-precise vertex would have had to expand
    #   it, which is forbidden.
    blocked_b = lambda s: is_mprecise(s, B, g)
    dist_b, neg2 = spfa(start, adj, seen, blocked=blocked_b)
    K_b = min((dist_b[gg] for gg in goals), default=None)
    # sanity: how many M-precise vertices, how many are goals
    mprec = [v for v in seen if is_mprecise(v, B, g)]
    mprec_nongoal = [v for v in mprec if not is_goal(v, B)]
    return {"M": M, "g": g, "Q": Q, "B": B, "R0": B - g, "incomplete": inc,
            "neg_all": neg1, "neg_b": neg2, "n_states": len(seen),
            "n_goals": len(goals), "n_mprecise": len(mprec),
            "n_mprecise_nongoal": len(mprec_nongoal),
            "K_all": K_all, "K_b": K_b}

if __name__ == "__main__":
    print("ANGLE D1 — case-(b) kappa-floor on the faithful scaled analog.")
    print("M plays 'm+1'; IH level is M-1; gap g plays the real 22. Barrier target: kappa >= M.")
    print("Two-case salvage SURVIVES iff K_b >= M+1; FAILS-at-boundary iff K_b == M; ")
    print("BARRIER FALSE iff K_b < M.\n")
    plan = [
        (2, 2, [2, 3, 4, 5, 6, 7, 8]),
        (2, 3, [2, 3, 4, 5]),
        (2, 4, [2, 3, 4]),
        (3, 2, [2, 3, 4, 5]),
        (3, 3, [2, 3]),
        (4, 2, [2, 3, 4]),
    ]
    for (M, g, Qs) in plan:
        for Q in Qs:
            r = analyse(M, g, Q)
            if r["K_b"] is None:
                verdict = "no goal in slice"
            elif r["K_b"] < r["M"]:
                verdict = f"*** BARRIER FALSE (K_b={r['K_b']} < M={r['M']}) ***"
            elif r["K_b"] == r["M"]:
                verdict = f"SALVAGE FAILS@boundary (K_b={r['K_b']} == M)"
            else:
                verdict = f"salvage survives (K_b={r['K_b']} >= M+1)"
            inc = " [INC]" if r["incomplete"] else ""
            ncyc = " [NEGCYC]" if (r["neg_all"] or r["neg_b"]) else ""
            print(f"M={M} g={g} Q={Q}: B={r['B']} R0={r['R0']} st={r['n_states']:>7}{inc}{ncyc} "
                  f"goals={r['n_goals']} mprec(nongoal)={r['n_mprecise_nongoal']} "
                  f"K_all={r['K_all']} K_b={r['K_b']}  => {verdict}")
        print()
