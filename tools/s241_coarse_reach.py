"""
S241 — Coarsened reachable-orbit probe (ANGLE B2, evidence route).

GOAL. Decide constrained reachability of the "trap cylinder"
  T := { v : v.c ≡ 4 (mod 3^(R+v.j)) }    (dlog = 2, the UNIQUE deep one-edge source)
from InvStart(m), under the constraint "without first passing through a coarse-m-precise
vertex (c ≡ 1 mod 3^(22(m-1)+2 + j))".

Full modulus 3^(22m+2) is astronomical. We compute the COARSENED reachable residue orbit
mod 3^k for k = 2..K, a NECESSARY-CONDITION relaxation: project every edge to mod 3^k.

WHY THE PROJECTION IS A VALID OVER-APPROXIMATION (rigour note).
The inverse-graph c-transitions are:
  one-edge  : c' ≡ 2^{-τ} · c                (mod 3^(R+j)),  τ=τ(α), keep iff c'%9 = α
  zero-edge : c' ≡ 2^{-τ} · (3c+1)           (mod 3^(R+j+1)), keep iff c'%9 = α, j↦j+1
For k ≤ R, 3^k | 3^(R+j) and 3^k | 3^(R+j+1), so BOTH congruences descend to mod 3^k:
the map "c mod 3^k ↦ c' mod 3^k" is well-defined. The admissibility filter c'%9=α is a
mod-9 = mod-3^2 condition, hence EXACTLY representable for k ≥ 2. Therefore the residue-level
graph mod 3^k (with j tracked separately, capped by budget Q) is an EXACT quotient of the
real inverse graph under c ↦ c mod 3^k. Reachability in the real graph IMPLIES reachability
in the quotient. So:
  * trap UNREACHABLE in the quotient  ==> trap UNREACHABLE in reality  (a real barrier, if it holds)
  * trap REACHABLE   in the quotient  ==> NECESSARY only, must inspect whether the constraint
    (no prior m-precise vertex) blocks every witness.

We track, per (k, j): reachable c-residues mod 3^k, their dlog (base 2) residues, whether
the trap residue 4 (deep, i.e. the actual residue value 4 mod 3^k, NOT just mod 9) is reached,
and — crucially — whether every path to a deep-trap residue must pass a coarse m-precise vertex.
"""

from __future__ import annotations
from collections import deque
from typing import Dict, Set, Tuple, List, Optional

ADMISSIBLE = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}

# aS202 = 1 + 3^22 exactly (verified in repo: PeriodicBlocks.lean aS202 = 31381059610).
AS202 = 1 + 3**22
assert AS202 == 31381059610


def inv2pow(t: int, M: int) -> int:
    return pow(pow(2, t, M), -1, M)


def dlog_base2(c: int, k: int) -> Optional[int]:
    """Discrete log of c base 2 mod 3^k (2 is a primitive root; order 2*3^(k-1)).
    Returns None if c not a unit."""
    M = 3**k
    if c % 3 == 0:
        return None
    order = 2 * 3**(k - 1)
    x = 1
    for t in range(order):
        if x == c % M:
            return t
        x = (x * 2) % M
    return None


def build_quotient_reach(m: int, k: int, Q: int, max_states: int = 5_000_000):
    """
    Exact quotient reachable set mod 3^k from InvStart(m), j-budget Q.
    Working at the (m)-cylinder: R = 22*m + 2 (matches InvStart(m)).
    State = (j, cres) with cres = c mod 3^k.
    Returns dict of reached states with provenance for the constraint analysis.
    """
    R = 22 * m + 2
    Mk = 3**k
    # start residue
    start_c = AS202 % Mk
    start = (0, start_c)

    # The coarse m-precise level for the constraint: a vertex is "coarse m-precise"
    # (the thing the suffix must avoid) if c ≡ 1 mod 3^(22(m-1)+2 + j).
    # In the (m+1)-residual language with M:=m+1, "m-precise" = c≡1 mod 3^(22m+2+j).
    # Here we are running from InvStart(m); the matching coarse level is one block down:
    # Rcoarse = 22*(m-1)+2.  We track the coarse-precise predicate at projection depth
    #   kc = Rcoarse + j  (clamped to k): c ≡ 1 mod 3^min(k, Rcoarse+j).
    # Since our residue is only mod 3^k, we can DETECT coarse-precision only up to depth k.
    # For the constraint test we therefore use the strongest detectable level: kc = k (full
    # available precision). A vertex is flagged 'cprecise' iff cres ≡ 1 mod 3^k AND this is a
    # genuine 1 (the deepest we can see). This is the RIGHT object: "c ≡ 1 at our resolution".
    # (At resolution k, "coarse m-precise" and "fine (m+1)-precise" coincide; the 22-digit gap
    #  between them is INVISIBLE at small k — exactly the phenomenon under study. We report this.)

    # forward (inverse-graph) transition on residues
    def succ(state):
        j, c = state
        out = []
        # one-edges (same j)
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            cp = (inv2pow(t, Mk) * c) % Mk
            if cp % 9 == alpha:
                out.append(((j, cp), +1, 'one', t))
        # zero-edges (j -> j+1), only if j < Q
        if j < Q:
            val = (3 * c + 1) % Mk
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                cp = (inv2pow(t, Mk) * val) % Mk
                if cp % 9 == alpha:
                    kappa = +1 if False else (-1 if t == 1 else 0)
                    out.append(((j + 1, cp), kappa, 'zero', t))
        return out

    # BFS, recording for each state the minimal "did any path reach it WITHOUT passing a
    # coarse-precise intermediate (other than possibly itself)". We compute two reachable sets:
    #   reach_all   : reachable at all
    #   reach_clean : reachable by a path whose INTERIOR (all vertices strictly before it,
    #                 and itself unless it is the goal/trap) contains NO coarse-precise vertex.
    # 'clean' = the constrained reachability (the device's hypothesis).
    reach_all: Set[Tuple[int, int]] = set()
    reach_clean: Set[Tuple[int, int]] = set()
    dist: Dict[Tuple[int, int], int] = {}

    def is_cprecise_resK(c):
        # coarse-precise as detectable at resolution k: c ≡ 1 mod 3^k
        return c % Mk == 1

    # start
    reach_all.add(start)
    dist[start] = 0
    # start clean iff start itself is not coarse-precise (aS202 mod 9 =1 but mod 3^k for k>=23
    # it's 1+3^22; for k<=22 it's 1 -> start IS c-precise at resolution k<=22!). Record honestly.
    start_cprec = is_cprecise_resK(start_c)
    if not start_cprec:
        reach_clean.add(start)

    # BFS over reach_all
    q = deque([start])
    while q:
        s = q.popleft()
        if len(reach_all) > max_states:
            return {"status": "incomplete", "states": len(reach_all)}
        for (sp, kappa, kind, t) in succ(s):
            if sp not in reach_all:
                reach_all.add(sp)
                dist[sp] = dist[s] + 1
                q.append(sp)

    # Separate BFS for clean reachability: a state is clean-reachable if there is a path
    # start -> ... -> state where NO vertex strictly before `state` is coarse-precise.
    # (We allow `state` itself to be coarse-precise — we just don't allow passing THROUGH one
    #  earlier.) Equivalently: BFS on the subgraph obtained by deleting outgoing edges from
    #  every coarse-precise vertex.
    q = deque()
    if start in reach_clean:
        q.append(start)
    elif not start_cprec:
        reach_clean.add(start); q.append(start)
    while q:
        s = q.popleft()
        # if s is coarse-precise, do NOT expand (passing through it is forbidden)
        if is_cprecise_resK(s[1]) and s != start:
            continue
        for (sp, kappa, kind, t) in succ(s):
            if sp not in reach_clean:
                reach_clean.add(sp)
                q.append(sp)

    # Analyse trap reachability.
    # Trap (deep): c ≡ 4 mod 3^k  (the ACTUAL residue 4, dlog=2 deep), at any j.
    trap_all = sorted([s for s in reach_all if s[1] == 4 % Mk])
    trap_clean = sorted([s for s in reach_clean if s[1] == 4 % Mk])
    # Also: the mod-9 trap class (c%9==4) — common, for contrast.
    trap9_all = sorted({(j, c % 9) for (j, c) in reach_all if c % 9 == 4})

    # dlog residues reached, per j
    dlogset: Dict[int, Set[int]] = {}
    cres_by_j: Dict[int, Set[int]] = {}
    for (j, c) in reach_all:
        cres_by_j.setdefault(j, set()).add(c)
    dl_by_j: Dict[int, Set[int]] = {}
    for j, cs in cres_by_j.items():
        s2 = set()
        for c in cs:
            d = dlog_base2(c, k)
            if d is not None:
                s2.add(d)
        dl_by_j[j] = s2

    # coarse-precise (c≡1) reachable vertices
    cprec_all = sorted([s for s in reach_all if is_cprecise_resK(s[1])])

    return {
        "status": "ok",
        "m": m, "k": k, "Q": Q, "R": R, "Mk": Mk,
        "start_c": start_c, "start_cprecise_resK": start_cprec,
        "n_reach_all": len(reach_all),
        "n_reach_clean": len(reach_clean),
        "trap_all": trap_all,          # deep trap c≡4 mod 3^k reachable (j-list)
        "trap_clean": trap_clean,      # deep trap reachable WITHOUT prior c≡1
        "trap9_all": trap9_all,        # mod-9 trap class (for contrast)
        "cprec_all": cprec_all,        # c≡1 mod 3^k reachable
        "cres_by_j": {j: sorted(cs) for j, cs in cres_by_j.items()},
        "dl_by_j": {j: sorted(s) for j, s in dl_by_j.items()},
    }


if __name__ == "__main__":
    print("aS202 =", AS202, "= 1 + 3^22 ;  aS202 % 9 =", AS202 % 9)
    print("dlog(aS202 mod 3^k) for k=2..6:",
          [dlog_base2(AS202 % 3**k, k) for k in range(2, 7)])
    print()
    for m in [1, 2, 3]:
        for k in range(2, 7):
            Q = 10
            r = build_quotient_reach(m, k, Q, max_states=3_000_000)
            if r["status"] != "ok":
                print(f"m={m} k={k}: {r}")
                continue
            print(f"=== m={m}  k={k}  (R={r['R']}, Mk=3^{k})  Q={Q} ===")
            print(f"  reach_all={r['n_reach_all']}  reach_clean={r['n_reach_clean']}"
                  f"  start_c={r['start_c']}  start_cprecise@resK={r['start_cprecise_resK']}")
            print(f"  DEEP trap (c==4 mod 3^{k}) reachable at j: {[s[0] for s in r['trap_all']]}")
            print(f"  DEEP trap reachable CLEAN (no prior c==1): {[s[0] for s in r['trap_clean']]}")
            print(f"  c==1 (coarse-precise) reachable at j: {sorted({s[0] for s in r['cprec_all']})}")
            print(f"  mod-9 trap class (c%9==4) reached at j: {sorted({j for (j,_) in r['trap9_all']})}")
        print()
