"""
S241 — FAITHFUL constrained-reachability test (ANGLE B2), correct indexing.

Cylinder index M (run from InvStart(M), working level B=22M+2). The residual constraint is the
'(M-1)-precise' predicate: a vertex (j,c) is FORBIDDEN-to-pass-through iff c ≡ 1 mod 3^(R0+j),
R0 = 22(M-1)+2.  The deep one-edge-to-goal SOURCE is the trap T: c ≡ 4 mod 3^(B+j) (dlog=2).

CORRECT START HANDLING.  Start residue = aS202 mod 3^k with aS202 = 1+3^22 (NOT reduced to 1).
The k<R0 'clean=0' seen earlier was an ARTIFACT: at resolution k<R0 the start's coarse shadow is 1,
falsely flagging it forbidden.  Faithfulness REQUIRES k ≥ R0.  For M=2, R0=24; for M=3, R0=46.

TRACTABILITY.  Full BFS at k≥24 is ~3^k states (intractable).  Instead we BOUND THE PATH LENGTH
(iterative deepening) and the zero-budget Q.  Branching ≤ 6/step, so depth-D search is ≤ 6^D but
heavily pruned by the visited set on (j, c mod 3^k) and by the forbidden-sink rule.  We search for
ANY clean path from start to a deep-trap residue, resolving the trap to the available depth:
  trap detect: c ≡ 4 mod 3^min(k, B+j)   (exact deep trap if k≥B+j; else the necessary shadow).

We report, per (M, k, Q, depthcap): whether a CLEAN path to the trap shadow EXISTS, its length,
and whether an UNCONSTRAINED one exists (sanity).  We push k from R0 upward as far as tractable.
"""

from __future__ import annotations
from collections import deque
from typing import Dict, Set, Tuple, List, Optional

ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}
AS202 = 1 + 3**22


def inv2pow(t: int, M: int) -> int:
    return pow(pow(2, t, M), -1, M)


def succ_residues(j, c, Mk, Q):
    out = []
    for alpha in ADMISSIBLE:
        t = TAU[alpha]
        cp = (inv2pow(t, Mk) * c) % Mk
        if cp % 9 == alpha:
            out.append((j, cp, +1))
    if j < Q:
        val = (3 * c + 1) % Mk
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            cp = (inv2pow(t, Mk) * val) % Mk
            if cp % 9 == alpha:
                out.append((j + 1, cp, -1 if t == 1 else 0))
    return out


def faithful_search(M, k, Q, depthcap, clean=True, max_visit=8_000_000):
    """
    BFS (level = path length) from InvStart(M) at modulus 3^k, budget Q, up to depthcap edges.
    clean=True: treat forbidden vertices (c≡1 mod 3^min(k,R0+j)) as SINKS (don't expand them),
                but the start is allowed even if (it never is for M>=2).
    Returns: first (depth, state) reaching a deep-trap residue (c≡4 mod 3^min(k,B+j)), plus stats.
    """
    B = 22 * M + 2
    R0 = 22 * (M - 1) + 2
    Mk = 3**k
    start = (0, AS202 % Mk)

    def forbidden(state):
        j, c = state
        L = min(k, R0 + j)
        return c % (3**L) == 1

    def is_trap(state):
        j, c = state
        L = min(k, B + j)
        return c % (3**L) == 4

    assert not (clean and forbidden(start)), \
        f"start forbidden at k={k} (need k>=R0={R0}); start shadow={start[1]%3**min(k,R0)}"

    visited: Set[Tuple[int, int]] = {start}
    # BFS by depth
    frontier = [start]
    trap_hit = None
    depth = 0
    n_expand = 0
    while frontier and depth < depthcap:
        nxt = []
        for s in frontier:
            if clean and s != start and forbidden(s):
                continue  # sink
            n_expand += 1
            for (jp, cp, ka) in succ_residues(s[0], s[1], Mk, Q):
                sp = (jp, cp)
                if is_trap(sp):
                    if trap_hit is None:
                        trap_hit = (depth + 1, sp)
                if sp not in visited:
                    visited.add(sp)
                    nxt.append(sp)
            if len(visited) > max_visit:
                return {"M": M, "k": k, "Q": Q, "depthcap": depthcap, "clean": clean,
                        "incomplete": True, "n_visited": len(visited),
                        "trap_hit": trap_hit, "depth_reached": depth, "B": B, "R0": R0,
                        "k_ge_R0": k >= R0, "k_resolves_trap": k >= B}
        frontier = nxt
        depth += 1
        if trap_hit is not None:
            break
    return {"M": M, "k": k, "Q": Q, "depthcap": depthcap, "clean": clean,
            "incomplete": False, "n_visited": len(visited),
            "trap_hit": trap_hit, "depth_reached": depth, "B": B, "R0": R0,
            "k_ge_R0": k >= R0, "k_resolves_trap": k >= B}


def show(M, ks, Q, depthcap):
    B = 22 * M + 2; R0 = 22 * (M - 1) + 2
    print(f"###### M={M}  B={B}  R0(forbidden m-precise level)={R0}  Q={Q}  depthcap={depthcap}")
    for k in ks:
        faith = (k >= R0)
        tag = "FAITHFUL" if faith else "ARTIFACT(k<R0)"
        try:
            rc = faithful_search(M, k, Q, depthcap, clean=True)
        except AssertionError as e:
            print(f"  k={k:>3} [{tag}] CLEAN skipped: {e}")
            rc = None
        ru = faithful_search(M, k, Q, depthcap, clean=False)
        def fmt(r):
            if r is None: return "n/a"
            if r["trap_hit"] is None:
                return f"trap NOT reached (visited={r['n_visited']}, depth={r['depth_reached']}{' INC' if r['incomplete'] else ''})"
            d, st = r["trap_hit"]
            return f"trap reached @depth {d} (visited={r['n_visited']})"
        res_unc = fmt(ru)
        res_cln = fmt(rc)
        print(f"  k={k:>3} [{tag}] k_resolves_trap(k>=B)={k>=B}")
        print(f"        UNCONSTRAINED: {res_unc}")
        print(f"        CLEAN        : {res_cln}")
    print()


if __name__ == "__main__":
    # M=2: faithful needs k>=24. Push k = 24,25,26 with small Q and depthcap.
    show(2, [22, 24, 25, 26], Q=4, depthcap=24)
    # M=3: faithful needs k>=46 (intractable); show k=24 (artifact) + note.
    show(3, [24, 46], Q=3, depthcap=20)
