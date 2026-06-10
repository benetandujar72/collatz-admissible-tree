"""
S241 — Verify a clean trap-witness AND answer the SHARP residual question.

The residual FirstMPrecisionSuffixPositive fails iff there is an admissible kappa-path from
InvStart to a GOAL whose FIRST m-precise vertex `mid` satisfies kappa(suffix mid->goal) <= 0.
The binding failure is `mid == goal` (empty suffix, kappa2 = 0) OR a suffix with net kappa <= 0.

We reconstruct, in the EXACT scaled analog (w, Q), the full clean reachable tree to the GOAL
(c≡1 at working level), and for the discovered goal-reaching paths we compute:
  * the sequence of (j, c, edge_kind, tau, kappa);
  * the FIRST m-precise vertex `mid` (c≡1 mod 3^(R0+j));
  * kappa2 = sum of kappa on the suffix mid..goal;
  * whether mid == goal (the empty-suffix R1 trap).
We search specifically for a clean goal-path whose first-m-precise vertex is the goal itself
(=> device DEAD) or has kappa2 <= 0.
"""
from __future__ import annotations
from collections import deque
from typing import Dict, Set, Tuple, List, Optional

ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}

def inv2pow(t, M): return pow(pow(2, t, M), -1, M)

def succ_exact(j, c, B, Q):
    out = []
    M = 3**(B + j)
    for alpha in ADMISSIBLE:
        t = TAU[alpha]
        cp = (inv2pow(t, M) * c) % M
        if cp % 9 == alpha:
            out.append((j, cp, 'one', t, +1))
    if j < Q:
        M1 = 3**(B + j + 1)
        val = (3 * c + 1) % M1
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            cp = (inv2pow(t, M1) * val) % M1
            if cp % 9 == alpha:
                out.append((j + 1, cp, 'zero', t, -1 if t == 1 else 0))
    return out

def analyse(w, Q, max_states=4_000_000):
    R0, B = w + 2, 2 * w + 2
    start = (0, (1 + 3**w) % 3**B)
    def forb(s):
        j, c = s; return c % 3**(R0 + j) == 1
    def is_goal(s):
        j, c = s; return c % 3**(B + j) == 1
    def is_trap(s):
        j, c = s; return c % 3**(B + j) == 4
    assert not forb(start)
    # clean BFS to ALL reachable (forbidden = sinks), record parent + edge meta + depth
    par: Dict[Tuple, Tuple] = {start: (None, None, None, 0, 0)}  # (prev, kind, tau, kappa, depth)
    q = deque([start])
    goals, traps = [], []
    incomplete = False
    while q:
        if len(par) > max_states:
            incomplete = True; break
        s = q.popleft()
        if is_goal(s): goals.append(s)
        if is_trap(s): traps.append(s)
        if s != start and forb(s):
            continue
        for (jp, cp, kind, t, ka) in succ_exact(*s, B, Q):
            sp = (jp, cp)
            if sp not in par:
                par[sp] = (s, kind, t, ka, par[s][4] + 1)
                q.append(sp)
    def path(target):
        seq = []
        cur = target
        while cur is not None:
            prev, kind, t, ka, depth = par[cur]
            seq.append((cur, kind, t, ka))
            cur = prev
        return list(reversed(seq))
    # for each clean goal, find first m-precise vertex and suffix kappa
    results = []
    for g in goals:
        p = path(g)
        # find first index (after start) that is m-precise (forb) — note goal is m-precise
        first_mp_idx = None
        for i, (v, kind, t, ka) in enumerate(p):
            if forb(v):
                first_mp_idx = i; break
        if first_mp_idx is None:
            continue
        mid = p[first_mp_idx][0]
        # kappa2 = sum of edge kappas strictly AFTER mid (edges leading into vertices after mid)
        kappa2 = sum(p[i][3] for i in range(first_mp_idx + 1, len(p)))
        results.append({
            "goal": g, "len": len(p) - 1, "mid": mid, "mid_is_goal": (mid == g),
            "first_mp_idx": first_mp_idx, "kappa2": kappa2,
        })
    # summarise: any clean goal with mid==goal (empty suffix) or kappa2<=0 ?
    dead_empty = [r for r in results if r["mid_is_goal"]]
    dead_kneg = [r for r in results if (not r["mid_is_goal"]) and r["kappa2"] <= 0]
    return {
        "w": w, "Q": Q, "R0": R0, "B": B,
        "n_clean_goals": len(goals), "n_clean_traps": len(traps),
        "n_dead_empty_suffix": len(dead_empty),
        "n_dead_kappa2_le0": len(dead_kneg),
        "min_kappa2": (min((r["kappa2"] for r in results), default=None)),
        "example_dead_empty": dead_empty[0] if dead_empty else None,
        "example_dead_kneg": dead_kneg[0] if dead_kneg else None,
        "all_goal_kappa2": sorted({r["kappa2"] for r in results}),
        "incomplete": incomplete, "n_states": len(par),
    }

if __name__ == "__main__":
    print("Verifying the SHARP residual on the faithful scaled analog (w=22 == M=2).")
    print("Device DEAD iff some clean goal-path has first-m-precise == goal (empty suffix) OR kappa2<=0.\n")
    # tractability: total reachable ~ 3^(B+Q-1) = 3^(2w+1+Q); keep 2w+1+Q <= 13.
    plan = {2: range(1, 8), 3: range(1, 6), 4: range(1, 4), 5: range(1, 2)}
    for w in plan:
        for Q in plan[w]:
            r = analyse(w, Q)
            flag = ""
            if r["n_dead_empty_suffix"] > 0: flag += " <<< EMPTY-SUFFIX (kappa2=0) DEVICE DEAD"
            if r["n_dead_kappa2_le0"] > 0: flag += " <<< kappa2<=0 DEVICE DEAD"
            inc = " [INC]" if r["incomplete"] else ""
            print(f"w={w} Q={Q}: B={r['B']} R0={r['R0']} states={r['n_states']:>7}{inc} "
                  f"clean_goals={r['n_clean_goals']:>5} "
                  f"clean_traps={r['n_clean_traps']:>5} dead_empty={r['n_dead_empty_suffix']} "
                  f"dead_kneg={r['n_dead_kappa2_le0']} min_kappa2={r['min_kappa2']} "
                  f"goal_kappa2={r['all_goal_kappa2'][:8]}{flag}")
        print()
