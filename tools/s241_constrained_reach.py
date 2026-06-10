"""
S241 — Constrained reachability probe, CORRECTED resolution (ANGLE B2).

The first probe (s241_coarse_reach.py) revealed the central subtlety: aS202 = 1 + 3^22, so
aS202 ≡ 1 (mod 3^k) for ALL k ≤ 22.  Hence at any coarse resolution k ≤ 22 the START vertex is
itself "c ≡ 1" — indistinguishable from a coarse-m-precise vertex.  That is exactly the project's
"22-digit (depth 3^21) invisibility":  the [m, m+1) ternary window spans digits 22m+2 .. 22(m+1)+1,
a width-22 band that NO projection mod 3^k with k ≤ 22 can resolve.

CONSEQUENCE.  A meaningful constrained-reachability test needs k ≥ 23 so that the start residue
is 1 + 3^22 ≠ 1 and the start is NOT coarse-precise.  We then track THREE precision levels:

  working level   B+j      (here B = R = 22m+2 for InvStart(m)); GOAL = c ≡ 1 mod 3^(B+j).
  m-precise level R0+j     with R0 = B - 22 = 22(m-1)+2 ;  c ≡ 1 mod 3^(R0+j)
                            (= "coarse m-precise" — the vertex the canonical-split suffix must
                             come AFTER; the device dies iff the deep one-edge SOURCE, c≡4 at the
                             working level, is reachable WITHOUT first hitting such a vertex).

We compute the residue quotient mod 3^k (EXACT quotient for k ≥ 2, see rigour note in
s241_coarse_reach.py).  To see BOTH levels we need k ≥ B (to detect the working-level goal/trap)
— but B = 24 already for m=1, modulus 3^24, large.  We therefore separate concerns:

  (A) CONSTRAINT TEST at the m-precise level:  set k = R0 + jmax-ish, detect c≡1 mod 3^(R0+j).
      We test: is the DEEP one-edge source class (c≡4 mod 3^k, dlog=2) reachable by a path whose
      interior avoids every coarse-m-precise vertex (c≡1 mod 3^(R0+j))?
  (B) We sweep k upward through and past R0 = 22(m-1)+2 to watch the clean-reachability verdict
      STABILISE (or not) as resolution increases — the decisive evidence.

For m=1, R0 = 22*0+2 = 2, B = 24.  So the m-precise level is just mod 9 (!), and the working
goal is mod 3^24.  That asymmetry (1 block = the whole gap from 2 to 24) is the m=1 degeneracy.
We therefore ALSO run m=2 (R0=24, B=46) and m=3 (R0=46, B=68) where both levels are deep, and the
'clean' question is non-degenerate.  We cap k for tractability and report growth + verdict.
"""

from __future__ import annotations
from collections import deque
from typing import Dict, Set, Tuple, List, Optional

ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}
AS202 = 1 + 3**22


def inv2pow(t: int, M: int) -> int:
    return pow(pow(2, t, M), -1, M)


def run(m: int, k: int, Q: int, max_states: int = 4_000_000):
    """
    Exact residue quotient mod 3^k from InvStart(m), budget Q.
    Working level B = 22m+2.  m-precise level R0 = B-22 = 22(m-1)+2 (>=2).
    Detect coarse-m-precise at level min(k, R0+j): c ≡ 1 mod 3^min(k,R0+j).
    Detect deep trap source at the working level min(k, B+j): c ≡ 4 mod 3^min(k,B+j)
      AND (for the genuine deep trap) we require the detection depth to reach the working level,
      i.e. k >= B+j; otherwise we only see the mod-3^k shadow of the trap (necessary-only).
    'clean' reachability = reachable by a path whose vertices strictly-before are NOT
      coarse-m-precise (deleting out-edges of coarse-m-precise vertices).
    """
    B = 22 * m + 2
    R0 = B - 22                      # = 22(m-1)+2
    Mk = 3**k
    start_c = AS202 % Mk
    start = (0, start_c)

    def succ(state):
        j, c = state
        out = []
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            cp = (inv2pow(t, Mk) * c) % Mk
            if cp % 9 == alpha:
                out.append((j, cp))
        if j < Q:
            val = (3 * c + 1) % Mk
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                cp = (inv2pow(t, Mk) * val) % Mk
                if cp % 9 == alpha:
                    out.append((j + 1, cp))
        return out

    def is_coarse_precise(state):
        # c ≡ 1 mod 3^min(k, R0+j)  -- detectable only if k >= the level; else best effort at k.
        j, c = state
        lvl = min(k, R0 + j)
        return c % (3**lvl) == 1

    def is_deep_trap(state):
        # working-level deep trap: c ≡ 4 mod 3^(B+j). Detectable only if k >= B+j.
        j, c = state
        lvl = B + j
        if k < lvl:
            return None   # cannot resolve at this k
        return c % (3**lvl) == 4

    def is_shadow_trap(state):
        # mod-3^k shadow: c ≡ 4 mod 3^k (necessary-only when k < B+j)
        return state[1] == 4 % Mk

    # full reachable
    reach: Set[Tuple[int, int]] = set([start])
    q = deque([start])
    incomplete = False
    while q:
        if len(reach) > max_states:
            incomplete = True
            break
        s = q.popleft()
        for sp in succ(s):
            if sp not in reach:
                reach.add(sp)
                q.append(sp)

    # clean reachable (delete out-edges of coarse-precise vertices, except start)
    start_cprec = is_coarse_precise(start)
    cleanset: Set[Tuple[int, int]] = set()
    if not start_cprec:
        cleanset.add(start)
        q = deque([start])
        while q:
            if len(cleanset) > max_states:
                incomplete = True
                break
            s = q.popleft()
            if s != start and is_coarse_precise(s):
                continue  # forbidden to pass through
            for sp in succ(s):
                if sp not in cleanset:
                    cleanset.add(sp)
                    q.append(sp)

    # verdicts
    deep_trap_all = sorted([s for s in reach if is_deep_trap(s) is True])
    deep_trap_clean = sorted([s for s in cleanset if is_deep_trap(s) is True])
    shadow_trap_all = sorted({s[0] for s in reach if is_shadow_trap(s)})
    shadow_trap_clean = sorted({s[0] for s in cleanset if is_shadow_trap(s)})
    cprec_reach = sorted([s for s in reach if is_coarse_precise(s)])
    # working-level GOAL (c≡1 mod 3^(B+j)) reachable?
    def is_goal(state):
        j, c = state
        lvl = B + j
        if k < lvl: return None
        return c % (3**lvl) == 1
    goal_all = sorted([s for s in reach if is_goal(s) is True])
    goal_clean = sorted([s for s in cleanset if is_goal(s) is True])

    return {
        "m": m, "k": k, "Q": Q, "B": B, "R0": R0, "incomplete": incomplete,
        "start_c": start_c, "start_cprec": start_cprec,
        "n_reach": len(reach), "n_clean": len(cleanset),
        "deep_trap_all_j": [s[0] for s in deep_trap_all],
        "deep_trap_clean_j": [s[0] for s in deep_trap_clean],
        "shadow_trap_all_j": shadow_trap_all,
        "shadow_trap_clean_j": shadow_trap_clean,
        "cprec_reach_j": sorted({s[0] for s in cprec_reach}),
        "n_cprec_reach": len(cprec_reach),
        "goal_all_j": [s[0] for s in goal_all],
        "goal_clean_j": [s[0] for s in goal_clean],
        "k_resolves_working": (k >= B),
    }


def report(m, ks, Q, max_states=4_000_000):
    B = 22 * m + 2; R0 = B - 22
    print(f"########## m={m}   B(working)=22m+2={B}   R0(m-precise)=22(m-1)+2={R0}   Q={Q}")
    print(f"          start residue aS202 mod 3^k ; aS202=1+3^22, so start=1 for k<=22, =1+3^22 for k>=23")
    for k in ks:
        r = run(m, k, Q, max_states=max_states)
        inc = " [INCOMPLETE budget]" if r["incomplete"] else ""
        res = "YES" if r["k_resolves_working"] else "no(shadow only)"
        print(f"-- k={k:>3}  reach={r['n_reach']:>8} clean={r['n_clean']:>8}{inc}"
              f"  start_cprec={r['start_cprec']}  k>=B?{res}")
        print(f"     coarse-precise (c==1 @ R0+j) reachable at j: {r['cprec_reach_j']}  (count={r['n_cprec_reach']})")
        if r["k_resolves_working"]:
            print(f"     WORKING goal  (c==1 @ B+j) reach_all j: {r['goal_all_j']}   clean j: {r['goal_clean_j']}")
            print(f"     DEEP trap     (c==4 @ B+j) reach_all j: {r['deep_trap_all_j']}   clean j: {r['deep_trap_clean_j']}")
        else:
            print(f"     SHADOW trap   (c==4 @ 3^k) reach_all j: {r['shadow_trap_all_j']}   clean j: {r['shadow_trap_clean_j']}")
    print()


if __name__ == "__main__":
    # m=1 (degenerate: R0=2). Sweep k across the working level B=24.
    report(1, [2, 9, 20, 22, 23, 24, 25, 26], Q=6)
    # m=2 (non-degenerate: R0=24, B=46). Sweep k across R0 and watch clean verdict stabilise.
    report(2, [9, 22, 23, 24, 25, 26, 28, 30], Q=4)
    # m=3 (R0=46). Just probe the m-precise band.
    report(3, [22, 23, 24, 25, 26], Q=3)
