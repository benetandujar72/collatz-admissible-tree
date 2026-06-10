"""
S241 — The DECIDER (ANGLE B2).

Two complementary computations.

EXP 1.  Tractable quotient sweep (m=2,3): clean-reachability of the trap SHADOW at the
        m-precise level, k = 2 .. KMAX.  Watch the verdict stabilise as resolution grows.
        State space ~ 60*3^(k-2); KMAX chosen for tractability.

EXP 2.  m=1 full-precision settlement.  For m=1 the working level is B=24 and the m-precise
        level is R0=2 (= mod 9).  So "coarse-m-precise" = c ≡ 1 (mod 9).  We can compute the
        EXACT reachable set at the working modulus 3^24? No (too big).  Instead we use the EXACT
        quotient at increasing k and the SPECIAL structure: the constraint "avoid c≡1 mod 9"
        is a MOD-9 condition, fully visible at every k>=2.  So the clean/forbidden graph is the
        SAME at every resolution (deletion of out-edges of c≡1-mod-9 vertices).  We can therefore
        decide, at the mod-9 quotient already, whether the deep trap's mod-9 shadow (c≡4 mod 9)
        is clean-reachable — and then LIFT one level at a time to see if the deep residue 4
        (mod 3^k) stays clean-reachable as k grows toward 24.

KEY OUTPUTS:
  * EXP2 mod-9 transfer graph: adjacency on the 6 admissible classes, with the c≡1 node as a
    SINK (no clean out-edges).  Decides whether c≡4 (mod 9) is reachable from start (≡1) WITHOUT
    re-entering ≡1.  This is the exact m=1 constraint at the coarsest level.
  * EXP2 lifted: clean-reachability of residue 4 mod 3^k, k=2..KMAX, for m=1.
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
    """Inverse-graph successors on residue c mod Mk (quotient). Returns (j',c',kappa,kind,tau)."""
    out = []
    for alpha in ADMISSIBLE:
        t = TAU[alpha]
        cp = (inv2pow(t, Mk) * c) % Mk
        if cp % 9 == alpha:
            out.append((j, cp, +1, 'one', t))
    if j < Q:
        val = (3 * c + 1) % Mk
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            cp = (inv2pow(t, Mk) * val) % Mk
            if cp % 9 == alpha:
                kappa = -1 if t == 1 else 0
                out.append((j + 1, cp, kappa, 'zero', t))
    return out


def exp2_mod9_transfer():
    """m=1 constraint at coarsest level R0=2 (mod 9). c≡1 mod 9 is the forbidden (sink) class.
    Build adjacency on classes {1,2,4,5,7,8}; report clean-reachability of class 4 from class 1."""
    Mk = 9
    Q = 10**9  # j unbounded for the class graph (mod 9 doesn't depend on modulus-lift beyond 9)
    # NOTE: zero-edge at mod 9 uses Mk=9; one-edge too. j only gates zero-edges; with Q huge both fire.
    classes = ADMISSIBLE
    adj = {a: [] for a in classes}
    for a in classes:
        # successors of any vertex with c≡a mod 9 (residue a itself as representative)
        for (jp, cp, kappa, kind, t) in succ_residues(0, a, Mk, Q):
            adj[a].append((cp, kappa, kind, t))
    # clean reachability from start class 1, with class 1 a SINK (no out-edges when reached, except start)
    start = 1
    forbidden = lambda c: (c == 1)
    clean = {start}
    q = deque([start])
    while q:
        a = q.popleft()
        if a != start and forbidden(a):
            continue
        for (cp, kappa, kind, t) in adj[a]:
            if cp not in clean:
                clean.add(cp); q.append(cp)
    # also unconstrained reachability
    allr = {start}; q = deque([start])
    while q:
        a = q.popleft()
        for (cp, kappa, kind, t) in adj[a]:
            if cp not in allr:
                allr.add(cp); q.append(cp)
    return {"adj": adj, "clean_reach": sorted(clean), "all_reach": sorted(allr),
            "class4_clean": (4 in clean), "class4_all": (4 in allr)}


def exp_quotient(m, k, Q, forbidden_level_fn, max_states=3_000_000):
    """EXACT quotient mod 3^k from InvStart(m). forbidden_level_fn(j) returns the precision level
    L(j) such that a vertex (j,c) is 'coarse-m-precise' iff c ≡ 1 mod 3^min(k,L(j)).
    Returns clean & all reachability of the deep-trap SHADOW (c==4 mod 3^k) and of c==1 shadows."""
    B = 22 * m + 2
    Mk = 3**k
    start = (0, AS202 % Mk)

    def forbidden(state):
        j, c = state
        L = min(k, forbidden_level_fn(j))
        return c % (3**L) == 1

    # all reachable
    allr = {start}; q = deque([start]); inc = False
    while q:
        if len(allr) > max_states: inc = True; break
        s = q.popleft()
        for (jp, cp, ka, kd, t) in succ_residues(s[0], s[1], Mk, Q):
            sp = (jp, cp)
            if sp not in allr:
                allr.add(sp); q.append(sp)
    # clean reachable
    clean = set();
    if not forbidden(start):
        clean = {start}; q = deque([start])
        while q:
            if len(clean) > max_states: inc = True; break
            s = q.popleft()
            if s != start and forbidden(s): continue
            for (jp, cp, ka, kd, t) in succ_residues(s[0], s[1], Mk, Q):
                sp = (jp, cp)
                if sp not in clean:
                    clean.add(sp); q.append(sp)
    trap_all = sorted({j for (j, c) in allr if c == 4 % Mk})
    trap_clean = sorted({j for (j, c) in clean if c == 4 % Mk})
    return {"m": m, "k": k, "Q": Q, "B": B, "incomplete": inc,
            "start": start, "start_forbidden": forbidden(start),
            "n_all": len(allr), "n_clean": len(clean),
            "trap_shadow_all_j": trap_all, "trap_shadow_clean_j": trap_clean}


if __name__ == "__main__":
    print("="*78)
    print("EXP 2a — m=1 constraint at coarsest level (mod 9): the class transfer graph")
    print("         forbidden/sink class = {c ≡ 1 mod 9}; start = class 1.")
    print("="*78)
    e = exp2_mod9_transfer()
    print("  mod-9 adjacency (class -> [(target_class, kappa, kind, tau), ...]):")
    for a in ADMISSIBLE:
        print(f"    [{a}] -> {e['adj'][a]}")
    print(f"  unconstrained reachable classes from 1: {e['all_reach']}")
    print(f"  CLEAN reachable classes from 1 (class 1 = sink): {e['clean_reach']}")
    print(f"  >>> deep-trap class 4 reachable unconstrained? {e['class4_all']}")
    print(f"  >>> deep-trap class 4 reachable CLEAN (no re-entry to class 1)? {e['class4_clean']}")
    print()

    print("="*78)
    print("EXP 2b — m=1 lifted: clean-reachability of residue 4 mod 3^k as k grows (R0=2).")
    print("         forbidden = c≡1 mod 9 (R0=2 constant). Watch residue-4 clean verdict vs k.")
    print("="*78)
    for k in range(2, 13):
        r = exp_quotient(1, k, Q=8, forbidden_level_fn=lambda j: 2, max_states=3_000_000)
        inc = " [INCOMPLETE]" if r["incomplete"] else ""
        print(f"  m=1 k={k:>2}: all={r['n_all']:>8} clean={r['n_clean']:>8}{inc} "
              f"start_forbidden={r['start_forbidden']}  "
              f"trap4 all_j={r['trap_shadow_all_j']}  clean_j={r['trap_shadow_clean_j']}")
    print()

    print("="*78)
    print("EXP 1 — m=2,3: clean-reachability of trap shadow at m-precise level R0=22(m-1)+2.")
    print("         forbidden = c≡1 mod 3^min(k, R0+j). Watch verdict stabilise vs k.")
    print("="*78)
    for m in [2, 3]:
        R0 = 22 * (m - 1) + 2
        print(f"  --- m={m}, R0={R0}, B={22*m+2} ---")
        for k in range(2, 12):
            r = exp_quotient(m, k, Q=6, forbidden_level_fn=lambda j, R0=R0: R0 + j,
                             max_states=3_000_000)
            inc = " [INC]" if r["incomplete"] else ""
            print(f"    k={k:>2}: all={r['n_all']:>8} clean={r['n_clean']:>8}{inc} "
                  f"start_forbidden={r['start_forbidden']}  "
                  f"trap4 all_j={r['trap_shadow_all_j']}  clean_j={r['trap_shadow_clean_j']}")
        print()
