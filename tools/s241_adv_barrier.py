"""
ADVERSARIAL independent check of the TWO barrier claims of the B2 finding:
  (C1) K*_goal = M (=2) exactly, K*_trap = M-1 (=1).  [min total kappa]
  (C2) EVERY split with a genuine intermediate (mid != goal) m-precise vertex has kappa2 >= 4 > 0
       i.e. the device fails ONLY on the empty-suffix (mid=goal).

The s241_final method combines clean-kappa1(v) and global-min-kappa2(v) from possibly DIFFERENT
paths, so it may misstate kappa2 for a SINGLE realizing path.  I instead do the rigorous thing:

For (C2), the device hypothesis fixes mid = the FIRST m-precise vertex of the prefix.  So a
mid!=goal device-FAILURE means: there is a single start->goal path whose FIRST m-precise vertex v
is NOT the goal, and the suffix v->goal has kappa2 <= 0.  Equivalently (since the prefix to the
first m-precise vertex is by definition clean): v is CLEAN-reachable from start (v m-precise,
v!=goal), and from v there is a path to a goal with total kappa <= 0.  The suffix MAY pass through
further m-precise vertices (the device only constrains the FIRST one) -- so global-min-kappa2 from v
IS the right quantity for the suffix.  Hence the s241_final formulation is actually correct for the
DEVICE question.  I re-derive it independently and ALSO report the exact min over a TRUE single-path
realization as a cross-check (min over clean-reachable m-precise v!=goal of dist_b[v]).

I additionally verify the SCALING of K*_goal and K*_trap is the *tight* M / M-1 (not just >=).
"""
from collections import deque

X = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}


def inv2(t, M):
    return pow(pow(2, t, M), -1, M)


def succ(j, c, B, Q):
    out = []
    M = 3 ** (B + j)
    for a in X:
        t = TAU[a]
        cp = (inv2(t, M) * c) % M
        if cp % 9 == a:
            out.append(((j, cp), +1))
    if j < Q:
        M1 = 3 ** (B + j + 1)
        val = (3 * c + 1) % M1
        for a in X:
            t = TAU[a]
            cp = (inv2(t, M1) * val) % M1
            if cp % 9 == a:
                out.append(((j + 1, cp), -1 if t == 1 else 0))
    return out


def spfa(adj, sources, nstates):
    INF = float('inf'); dist = {s: 0 for s in sources}
    dq = deque(sources); inq = set(sources); cnt = {}
    neg = False
    while dq:
        u = dq.popleft(); inq.discard(u); du = dist[u]
        for (vv, ka) in adj.get(u, []):
            if du + ka < dist.get(vv, INF):
                dist[vv] = du + ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv] = cnt.get(vv, 0) + 1
                    if cnt[vv] > nstates:
                        neg = True; dq.clear(); break
    return dist, neg


def analyse(w, Q, max_states=4_000_000):
    R0, B = w + 2, 2 * w + 2
    start = (0, (1 + 3 ** w) % 3 ** B)
    isg = lambda s: s[1] % 3 ** (B + s[0]) == 1 and s[0] >= 1
    ist = lambda s: s[1] % 3 ** (B + s[0]) == 4 and s[0] >= 1
    forb = lambda s: s[1] % 3 ** (R0 + s[0]) == 1
    adj = {}; q = deque([start]); seen = {start}; inc = False
    while q:
        if len(seen) > max_states:
            inc = True; break
        s = q.popleft(); e = succ(*s, B, Q); adj[s] = e
        for (sp, ka) in e:
            if sp not in seen:
                seen.add(sp); q.append(sp)
    radj = {}
    for u in adj:
        for (vv, ka) in adj[u]:
            radj.setdefault(vv, []).append((u, ka))
    goals = [v for v in seen if isg(v)]
    traps = [v for v in seen if ist(v)]
    dist_f, negf = spfa(adj, [start], len(seen))
    K_goal = min((dist_f.get(g, float('inf')) for g in goals), default=None)
    K_trap = min((dist_f.get(t, float('inf')) for t in traps), default=None)
    dist_b, negb = spfa(radj, goals, len(seen))  # min kappa v->goal
    # clean kappa1: SPFA with forbidden as sink
    INF = float('inf'); dist_c = {start: 0}; dq = deque([start]); inq = {start}; cnt = {}
    while dq:
        u = dq.popleft(); inq.discard(u)
        if u != start and forb(u):
            continue
        du = dist_c[u]
        for (vv, ka) in adj.get(u, []):
            if du + ka < dist_c.get(vv, INF):
                dist_c[vv] = du + ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv] = cnt.get(vv, 0) + 1
                    if cnt[vv] > len(seen):
                        dq.clear(); break
    # device failure mid != goal: clean-reachable m-precise v, v not a goal, with min suffix kappa2<=0
    threats = []
    for v in seen:
        if forb(v) and not isg(v) and v in dist_c and v in dist_b:
            threats.append((dist_b[v], dist_c[v], v))
    threats.sort()
    min_k2_mng = threats[0][0] if threats else None
    n_threats_le0 = sum(1 for (k2, _, _) in threats if k2 <= 0)
    return {
        "w": w, "Q": Q, "B": B, "R0": R0, "inc": inc, "negf": negf, "negb": negb,
        "n_states": len(seen), "n_goals": len(goals),
        "K_goal": K_goal, "K_trap": K_trap,
        "min_kappa2_midneqgoal": min_k2_mng,
        "n_midneqgoal_mprecise": len(threats),
        "n_midneqgoal_with_kappa2_le_0": n_threats_le0,
        "smallest5_kappa2_mng": [t[0] for t in threats[:5]],
    }


if __name__ == "__main__":
    print("INDEPENDENT barrier re-check.  Expect K_goal->2, K_trap->1, min_kappa2(mid!=goal)>0.\n")
    for (w, Qs) in [(2, [1, 2, 3, 4, 5, 6]), (3, [1, 2, 3])]:
        for Q in Qs:
            r = analyse(w, Q)
            print(f"w={w} Q={Q}: states={r['n_states']:>7}{' INC' if r['inc'] else ''} "
                  f"K_goal={r['K_goal']} K_trap={r['K_trap']} "
                  f"min_k2(mid!=goal)={r['min_kappa2_midneqgoal']} "
                  f"#mng_mprecise={r['n_midneqgoal_mprecise']} "
                  f"#mng_with_k2<=0={r['n_midneqgoal_with_kappa2_le_0']} "
                  f"neg_cycle={r['negf'] or r['negb']}")
        print()
