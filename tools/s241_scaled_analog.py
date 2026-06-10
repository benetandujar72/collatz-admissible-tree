"""
S241 — SCALED ANALOG: exact full-fidelity constrained reachability for a small block width w.

The real problem has block width 22 (aS202 = 1 + 3^22), working level B=22M+2, forbidden level
R0=22(M-1)+2 = B - 22.  The 22-digit gap forces modulus >= 3^24, intractable for EXACT BFS.

STRUCTURAL ANALOG.  Replace 22 by a small width w.  Define:
   a_w := 1 + 3^w                 (analog of aS202; ν3(a_w - 1) = w exactly)
   B    := w + 2 (+ extra)        working level for the analog 'InvStart' = a_w mod 3^B
   R0   := B - w                  forbidden ('m-precise') level
This reproduces EXACTLY the project's geometry — start ≡ 1 mod 3^(R0) but ≢ 1 mod 3^(R0+1)
(since the differing digit is at position w = B - R0), so the start ESCAPES the forbidden band by
one digit, just as aS202 does — but now 3^B is tractable (w=2..6 -> B up to ~10).

We compute the EXACT reachable set mod 3^(B+jmax) and decide:
  Q1. Is the deep trap  c ≡ 4 mod 3^(B+j)  (dlog=2, full working precision) reachable AT ALL?
  Q2. Is it reachable CLEAN (path interior avoids c ≡ 1 mod 3^(R0+j))?
  Q3. If clean-reachable, exhibit the shortest clean path (the witness) — this would mean the
      canonical-first-split device is DEAD at the analog scale, predicting death at scale 22.
  If NOT clean-reachable for all w -> evidence the device SURVIVES (the width-w band blocks it).

We sweep w and, for each, jmax (zero-budget). EXACT, no relaxation: modulus = 3^(B+jmax).
"""

from __future__ import annotations
from collections import deque
from typing import Dict, Set, Tuple, List, Optional

ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}


def inv2pow(t: int, M: int) -> int:
    return pow(pow(2, t, M), -1, M)


def succ(j, c, Mtop, Q):
    """Successors at the TOP modulus Mtop=3^(B+Q) (so all levels resolvable). Edge congruences
    are at level 3^(B+j) (one) and 3^(B+j+1) (zero); we compute c' uniquely mod 3^(B+j(+1)) and
    then it is only determined to THAT level — to stay exact we keep c reduced mod 3^(B+j)."""
    raise NotImplementedError


def build(w, Q, extra=0):
    """
    EXACT reachable graph. We track c at its NATURAL precision 3^(B+j) (the cylinder modulus),
    exactly as the Lean InvVertex does (c is a residue mod 3^(R+j)). So state=(j, c) with
    0<=c<3^(B+j).  One-edge keeps j, modulus 3^(B+j). Zero-edge raises j, modulus 3^(B+j+1).

    FAITHFUL GEOMETRY (mirrors M>=2): block width = w, forbidden level R0 = w+2, working
    level B = R0 + w = 2w+2.  Start = 1 + 3^w, whose differing digit (position w) lies BELOW
    R0 = w+2, so start mod 3^R0 = 1+3^w != 1 -> start ESCAPES the forbidden band by exactly the
    same mechanism as aS202 (w=22 -> R0=24=M2 forbidden level, B=46=M2 working level).
    """
    R0 = w + 2
    B = 2 * w + 2
    a_w = 1 + 3**w
    start_c = a_w % (3**B)
    start = (0, start_c)

    def succ_exact(j, c):
        out = []
        M = 3**(B + j)
        # one-edges: c' = 2^{-t} c mod M, keep iff c'%9==alpha
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            cp = (inv2pow(t, M) * c) % M
            if cp % 9 == alpha:
                out.append((j, cp, +1))
        # zero-edges: modulus M1=3^(B+j+1); c' = 2^{-t}(3c+1) mod M1
        if j < Q:
            M1 = 3**(B + j + 1)
            val = (3 * c + 1) % M1
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                cp = (inv2pow(t, M1) * val) % M1
                if cp % 9 == alpha:
                    out.append((j + 1, cp, -1 if t == 1 else 0))
        return out

    def forbidden(state):
        # m-precise: c ≡ 1 mod 3^(R0+j)
        j, c = state
        return c % (3**(R0 + j)) == 1

    def is_trap(state):
        # deep trap: c ≡ 4 mod 3^(B+j)  (full working precision, dlog=2)
        j, c = state
        return c % (3**(B + j)) == 4

    def is_goal(state):
        j, c = state
        return c % (3**(B + j)) == 1

    # full reachable + parent pointers for witness
    allr: Set[Tuple[int, int]] = {start}
    parent: Dict[Tuple[int, int], Optional[Tuple]] = {start: None}
    q = deque([start])
    while q:
        s = q.popleft()
        for (jp, cp, ka) in succ_exact(*s):
            sp = (jp, cp)
            if sp not in allr:
                allr.add(sp); parent[sp] = (s, ka); q.append(sp)

    # clean reachable + parent (forbidden vertices are sinks; start allowed)
    start_forb = forbidden(start)
    cleanr: Set[Tuple[int, int]] = set()
    cparent: Dict[Tuple[int, int], Optional[Tuple]] = {}
    if not start_forb:
        cleanr = {start}; cparent = {start: None}; q = deque([start])
        while q:
            s = q.popleft()
            if s != start and forbidden(s):
                continue
            for (jp, cp, ka) in succ_exact(*s):
                sp = (jp, cp)
                if sp not in cleanr:
                    cleanr.add(sp); cparent[sp] = (s, ka); q.append(sp)

    def witness(target, par):
        path = []
        cur = target
        while cur is not None and cur in par:
            path.append(cur)
            nb = par[cur]
            cur = nb[0] if nb is not None else None
        return list(reversed(path))

    traps_all = sorted([s for s in allr if is_trap(s)])
    traps_clean = sorted([s for s in cleanr if is_trap(s)])
    goals_all = sorted([s for s in allr if is_goal(s)])
    goals_clean = sorted([s for s in cleanr if is_goal(s)])

    # shortest clean trap witness (BFS already gives a tree; reconstruct one)
    wtn = None
    if traps_clean:
        # pick the trap with shortest reconstructed path
        best = None
        for t in traps_clean:
            p = witness(t, cparent)
            if best is None or len(p) < len(best):
                best = p
        wtn = best

    return {
        "w": w, "Q": Q, "B": B, "R0": R0, "a_w": a_w, "start": start,
        "start_forbidden": start_forb,
        "n_all": len(allr), "n_clean": len(cleanr),
        "traps_all": traps_all, "traps_clean": traps_clean,
        "goals_all_j": sorted({s[0] for s in goals_all}),
        "goals_clean_j": sorted({s[0] for s in goals_clean}),
        "clean_trap_witness": wtn,
    }


if __name__ == "__main__":
    print("SCALED ANALOG (faithful, mirrors M>=2): a_w=1+3^w, R0=w+2, B=2w+2.")
    print("forbidden = c≡1 mod 3^(R0+j); deep trap = c≡4 mod 3^(B+j).")
    print("Question: is the deep trap clean-reachable (path interior avoids forbidden)?  w=22 == M=2.\n")
    for w in range(2, 8):
        for Q in range(1, 7):
            r = build(w, Q)
            tw = r["clean_trap_witness"]
            twlen = (len(tw) - 1) if tw else None
            print(f"w={w} Q={Q}: B={r['B']} a_w={r['a_w']} start_forbidden={r['start_forbidden']} "
                  f"|all|={r['n_all']:>7} |clean|={r['n_clean']:>7} "
                  f"trap_all={'Y' if r['traps_all'] else 'N'}({len(r['traps_all'])}) "
                  f"trap_CLEAN={'Y' if r['traps_clean'] else 'N'}({len(r['traps_clean'])}) "
                  f"goals_clean_j={r['goals_clean_j']}")
            if r["traps_clean"]:
                # show one witness with edge kinds
                print(f"       CLEAN TRAP WITNESS (len {twlen}): {tw}")
        print()
