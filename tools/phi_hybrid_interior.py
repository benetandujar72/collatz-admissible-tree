"""
phi_hybrid_interior.py — prong A of GATE H (S243): the interior profile of the
Green+Hoelder hybrid class with the CORRECTED pole set.

The phi_realkam_lp interior analysis used Green targets 2^s*{1, 4, aS202}, s=0..5.
That set MISSES the -1 attractor (the tau=1 filament, identity 2(y+1) = 3(c+1))
at scales t >= 3.  A ball avoiding ALL targets has every nu3(c - target) constant
on it, so for Phi = g(nu3-features) + Hoelder(L, alpha) the whole within-ball jump
must be carried by the Hoelder part: g_int(t) < m at scale t forces
L >= (m - g_int) * 3^(alpha*t).

This script recomputes the interior profile at (m=1, Q) for three pole sets:
  P0: 2^s*{1, 4, a*},        s = 0..5   (the original)
  P1: 2^s*{1, -1, 4, a*},    s = 0..5   (the corrected attractor set)
  P2: 2^s*{±1, ±4, ±a*},     s = 0..8   (generous: orbit shifts + both signs)
If the interior breaks persist under P2, the death of "any g of nu3-features
towards boundedly many algebraically-natural poles + Hoelder remainder" is robust.

Usage: python phi_hybrid_interior.py [Q]    (default 5)
"""
from __future__ import annotations
import sys, json
from collections import defaultdict

sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from phi_realkam_lp import Region, hub_aggregates, POW3
from s202_engine import a202_mod

INF = float("inf")


def interior_profile(reg, ghub, gwit, targets_fn, label):
    """targets_fn(j, t) -> set of residues mod 3^t to avoid."""
    cache = {}
    prof = defaultdict(lambda: [INF, 0, None])
    for hidx, h in enumerate(reg.hubs):
        j, t = h["j"], h["t"]
        key = (j, t)
        tg = cache.get(key)
        if tg is None:
            tg = targets_fn(j, t)
            cache[key] = tg
        rep = h["reps"][0]
        while rep[0] == 'h':
            rep = reg.hubs[rep[1]]["reps"][0]
        c0 = reg.jc_of[rep[1]][1]
        if (c0 % POW3[t]) in tg:
            continue
        e = prof[t]
        e[1] += 1
        if ghub[hidx] < e[0]:
            e[0] = ghub[hidx]
            e[2] = hidx
    m = reg.m
    print(f"  [{label}] interior profile g_int(t):")
    deepest = None
    for t in sorted(prof):
        g, nh, hidx = prof[t]
        mark = ""
        if g < m:
            deepest = t
            if gwit[hidx] is not None:
                u, v = gwit[hidx]
                (ju, cu), (jv, cv) = reg.jc_of[u], reg.jc_of[v]
                mark = f"  <-- BREAKS (u at j{ju}, v at j{jv})"
        gs = f"{g:.0f}" if g < INF else "inf"
        print(f"    t={t:>2}: g_int={gs:>4}  (hubs={nh}){mark}")
    Lb = {}
    for a in (0.5, 1.0, 2.0):
        Lv = 0.0
        for t in sorted(prof):
            g = prof[t][0]
            if g < m:
                Lv = max(Lv, (m - g) * 3.0 ** (a * t))
        Lb[a] = Lv
    print(f"  [{label}] deepest interior break t={deepest}; "
          f"L_hybrid(alpha) >= " +
          ", ".join(f"{Lb[a]:.4g} (a={a})" for a in (0.5, 1.0, 2.0)))
    return {"deepest": deepest, "L_bound": Lb,
            "profile": {str(t): (None if v[0] == INF else v[0], v[1])
                        for t, v in sorted(prof.items())}}


def run(Q):
    print(f"=== interior profiles with corrected poles  m=1 Q={Q} ===", flush=True)
    reg = Region(1, Q)
    lab0, _ = reg.dijkstra(forward=True, hop=None, use_hops=False)
    dfwd0 = reg.fwd_cost(lab0)
    labr, _ = reg.dijkstra(forward=False, hop=None, use_hops=False)
    psi0 = reg.rev_cost(labr)
    ghub, gwit = hub_aggregates(reg, dfwd0, psi0)

    def mk(base_as, smax):
        def f(j, t):
            M = POW3[reg.R + j]
            astar = a202_mod(reg.R + j)
            out = set()
            for a in base_as:
                aa = astar if a == 'a' else (-astar if a == '-a' else a)
                for s in range(smax + 1):
                    out.add((pow(2, s, M) * aa) % POW3[t])
            return out
        return f

    res = {}
    res["P0_orig"] = interior_profile(
        reg, ghub, gwit, mk([1, 4, 'a'], 5), "P0: 2^s{1,4,a*} s<=5")
    res["P1_attractors"] = interior_profile(
        reg, ghub, gwit, mk([1, -1, 4, 'a'], 5), "P1: 2^s{1,-1,4,a*} s<=5")
    res["P2_generous"] = interior_profile(
        reg, ghub, gwit, mk([1, -1, 4, -4, 'a', '-a'], 8),
        "P2: 2^s{±1,±4,±a*} s<=8")
    return res


if __name__ == "__main__":
    Q = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    out = run(Q)
    p = r"C:\Users\benet\Downloads\collatz-admissible-tree\tools\phi_hybrid_interior_data.json"
    with open(p, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print(f"[written {p}]")
