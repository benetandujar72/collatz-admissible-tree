"""
ANGLE D1 — does the WEAKER target KappaPathSplit survive (even though BlockBoundaryExists is false)?

KappaPathSplit m Q (UniformBarrier.lean:204) demands, for EVERY (m+1)-goal-path P (kappa, vs):
   EXISTS a split P = prefix ++ suffix with  kappa = k1 + k2,  k1 >= m,  k2 >= 1.
Crucially it does NOT require the split point to be m-precise (unlike BlockBoundaryExists).

This is strictly WEAKER than BlockBoundaryExists and is ALL that barrier_step_of_split needs.
Question: is KappaPathSplit TRUE on the analog (for every minimal/extremal goal-path), even on the
case-(b) witness where no m-precise split exists?

A split with k1>=m, k2>=1 exists for a path of total kappa K and edge-kappa-sequence e_1..e_L iff
there is a prefix index p (1<=p<=L) with  sum(e_1..e_p) >= m  AND  sum(e_{p+1}..e_L) >= 1.
Equivalently: exists p with prefix_kappa[p] >= m and (K - prefix_kappa[p]) >= 1, i.e.
   m <= prefix_kappa[p] <= K-1.
So KappaPathSplit holds for THIS path iff the prefix-kappa walk hits the interval [m, K-1] at some
interior cut. Since the walk starts at 0 (empty prefix) and ends at K, and steps by {-1,0,+1}, it
hits every integer in [0,K] that it... NO: with -1 steps it can be non-monotone, but it DOES take
unit steps, so it hits EVERY integer value between consecutive extremes. The walk goes 0 -> K. If
K >= m+1, does it necessarily hit a value v with m <= v <= K-1 at an INTERIOR node? The final value
is K; the node before the last edge has kappa K - e_L. We need SOME interior prefix in [m,K-1].

We test directly: for the MINIMAL-kappa path to each goal (reconstructed), compute the prefix-kappa
walk and check whether an interior cut gives (k1>=m, k2>=1). We report the worst case: is there a
goal-path where NO such split exists (which would refute KappaPathSplit too)?

We focus on the EXTREMAL (min-kappa) path since that is the binding one (smallest K). If even K=m
(the floor) — then we need k1>=m and k2>=1 => k1+k2>=m+1 > m = K, IMPOSSIBLE. So at a floor goal
with K = m exactly, KappaPathSplit is FALSE for that path!  We check whether floor goals have K=m
(=> KappaPathSplit false) or K>=m+1.
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

def spfa(start, adj, seen):
    INF = float('inf'); dist = {v: INF for v in seen}; dist[start] = 0
    dq = deque([start]); inq = {start}; cnt = {start: 0}
    while dq:
        u = dq.popleft(); inq.discard(u); du = dist[u]
        for (vv, ka) in adj.get(u, []):
            if du + ka < dist[vv]:
                dist[vv] = du + ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv] = cnt.get(vv, 0) + 1
                    if cnt[vv] > len(seen) + 1: dq.clear(); break
    return dist

def analyse(M, g, Q, cap=2_000_000):
    B, start, adj, seen, inc = build(M, g, Q, cap)
    goal = lambda s: s[0] >= 1 and s[1] % 3 ** (B + s[0]) == 1 % 3 ** (B + s[0])
    goals = [v for v in seen if goal(v)]
    dist = spfa(start, adj, seen)
    Kmin = min((dist[gg] for gg in goals), default=None)
    # A floor goal with K=M: KappaPathSplit needs k1>=M-1? NO: KappaPathSplit m has k1>=m=M-1
    #   (since here M plays m+1, so 'm' = M-1). It needs k1>=M-1 and k2>=1, total>=M. Feasible iff K>=M.
    #   And a split exists iff the prefix-kappa walk hits [M-1, K-1] interior. Since steps are unit and
    #   walk 0->K, if K>=M it hits M-1 (<=K-1 as K>=M) at SOME node; if that node is interior, OK.
    # The ONLY failure: K = M-1 (< M) => impossible to have k1>=M-1 and k2>=1. But K>=M (barrier). And
    # K=M-1 would itself violate the (m+1)=M barrier. So as long as K>=M, KappaPathSplit is satisfiable
    # for the min path PROVIDED the walk reaches >=M-1 strictly before the end.
    mm = M - 1  # the 'm' in KappaPathSplit m (since M = m+1)
    return {"B": B, "inc": inc, "n": len(seen), "ngoal": len(goals),
            "Kmin": Kmin, "M": M, "m_in_split": mm,
            "Kmin_ge_M": (Kmin is not None and Kmin >= M),
            "Kmin_eq_M": (Kmin == M)}

if __name__ == "__main__":
    print("ANGLE D1 — KappaPathSplit feasibility on the analog (M plays m+1; split's 'm' = M-1).")
    print("KappaPathSplit needs, per path: k1 >= M-1 AND k2 >= 1 (total >= M).")
    print("At a FLOOR goal with total kappa K = M, this needs k1 in [M-1, M-1] and k2 = 1 at an")
    print("INTERIOR cut. Feasible iff the prefix-kappa walk reaches M-1 strictly before the goal.\n")
    for (M, g, Q) in [(2,2,4),(2,2,5),(2,2,6),(2,3,4),(2,3,5),(3,2,4),(3,2,5),(4,2,3)]:
        r = analyse(M, g, Q)
        inc = " INC" if r["inc"] else ""
        print(f"M={M} g={g} Q={Q}: st={r['n']:>8}{inc} goals={r['ngoal']} Kmin={r['Kmin']} "
              f"(M={M}, split-m={r['m_in_split']})  Kmin>=M:{r['Kmin_ge_M']}  Kmin==M:{r['Kmin_eq_M']}")
    print("\nNOTE: KappaPathSplit can STILL be true even when BlockBoundaryExists is false, because the")
    print("split point need NOT be m-precise. The open question becomes: does EVERY (m+1)-goal-path admit")
    print("SOME cut with k1>=m, k2>=1?  This is the genuinely weaker, still-open target.")
