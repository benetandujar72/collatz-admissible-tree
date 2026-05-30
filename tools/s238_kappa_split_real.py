"""
s238_kappa_split_real.py — confirm the split-failure phenomenon on the REAL
S202 inverse graph (no synthetic rewrite of the transition map).

We use the genuine S202Engine edges (m, Q real). The obstruction is that a true
(m+1)-goal c≡1 mod 3^(22(m+1)+2+j) is astronomically deep. So we test the
WEAKER but FAITHFUL question that already decides BlockBoundaryExists:

  Take the real graph at level (m+1) = 2 (base R = 22*2+2 = 46) is intractable.
  Instead we observe that BlockBoundaryExists is a statement purely about the
  κ-precise EDGE STRUCTURE and the predicate "projπ m v is an m-goal", i.e.
  v.c ≡ 1 (mod 3^(22m+2+j)).  The phenomenon that kills it — a single one-edge
  jumping ρ₊ across both the coarse (22m+2) and fine (22m+24) thresholds at once
  — is governed by the one-edge discrete-log law ρ₊(c') = ν₃(c−2^τ), which the
  real engine implements exactly.

  So we directly exhibit, in the REAL engine at small m and a SMALL coarse cap
  Kc (playing the role of 22m+2) versus fine cap Kf=Kc+22 (the real +22 jump),
  a reachable vertex v and an incoming one-edge from u such that:
      ρ₊(u.c, Kc+u.j) < Kc+u.j           (u NOT coarse-precise)
      ρ₊(v.c, Kf+v.j) = Kf+v.j           (v IS fine-precise, hence coarse too)
  i.e. ONE one-edge crosses both thresholds — the trivial-split trap, with the
  REAL +22 gap.

We scan the real reachable region (m=1) for such one-edges and report the
largest single-edge ρ₊ jump observed (Δρ₊). If Δρ₊ ≥ 22 occurs from a
sub-coarse vertex, the +22-gap trivial-split trap is realised in the true graph.
"""
from __future__ import annotations
from collections import deque
from s202_engine import S202Engine, State, ADMISSIBLE, TAU


def nu3(x: int) -> int:
    if x == 0:
        return 10**9
    x = abs(x)
    k = 0
    while x % 3 == 0:
        x //= 3
        k += 1
    return k


def rho_at(c: int, cap: int) -> int:
    return min(nu3(c - 1), cap)


def scan(m=1, Q=12, GAP=22, max_states=300000):
    """Scan real reachable region; for each one-edge u->v report the ρ₊ jump
    at the FINE cap and whether it crosses the coarse threshold from below."""
    eng = S202Engine(m=m, Q=Q)
    R = eng.R
    # BFS reachable region (optimistic cost cut like structure_probe)
    dist = {eng.start: 0}
    q = deque([eng.start])
    seen = {eng.start}
    T = 40  # generous threshold so we explore deep one-edge chains
    while q and len(seen) < max_states:
        s = q.popleft()
        d = dist[s]
        if d - (eng.Q - s.j) >= T:
            continue
        for (t, w) in eng.outgoing_edges(s):
            nd = d + w
            if nd - (eng.Q - t.j) >= T:
                continue
            if t not in seen:
                seen.add(t)
                dist[t] = nd
                q.append(t)
            elif nd < dist[t]:
                dist[t] = nd
                q.append(t)
    states = list(seen)

    # We let Kc (coarse cap base) sweep small values; fine = Kc + GAP.
    # ρ₊ is computed on the REAL c-values of the real graph.
    worst = []   # (delta_rho_fine, Kc, u, v, t)
    trap_hits = 0
    one_edge_count = 0
    for s in states:
        j, c = s.j, s.c
        M = eng.modulus(j)
        for a in ADMISSIBLE:
            t = TAU[a]
            y = (eng.inv_pow2(t, j) * c) % M
            if y % 9 != a:
                continue
            one_edge_count += 1
            v = State(j, y)   # one-edge target (same j)
            # sweep coarse base Kc; need Kc+j <= r so ρ₊ well-defined within M=3^(R+j).
            # Use Kc small relative to R so caps are < R+j (so c-values carry enough digits).
            for Kc in range(2, R + j - GAP):
                cap_c_u = Kc + j
                cap_f_v = Kc + GAP + j
                if cap_f_v > R + j:
                    break
                rho_u_coarse = rho_at(c, cap_c_u)       # u at coarse cap
                rho_v_fine = rho_at(y, cap_f_v)          # v at fine cap
                u_not_coarse = rho_u_coarse < cap_c_u
                v_is_fine = rho_v_fine == cap_f_v
                if u_not_coarse and v_is_fine:
                    # ONE one-edge crosses both coarse(Kc) and fine(Kc+GAP) thresholds
                    trap_hits += 1
                    if len(worst) < 12:
                        worst.append((Kc, j, c, y, t,
                                      rho_u_coarse, cap_c_u, rho_v_fine, cap_f_v))
                    break
    print(f"=== REAL S202 graph m={m} Q={Q}, GAP={GAP}, region={len(states)} states ===")
    print(f"  one-edges scanned: {one_edge_count}")
    print(f"  TRAP one-edges (u NOT coarse-precise at some Kc, but v fine-precise "
          f"at Kc+{GAP}): {trap_hits}")
    if worst:
        print("  examples (Kc, j, u.c, v.c, τ, ρ₊(u,coarse), coarse_cap, "
              "ρ₊(v,fine), fine_cap):")
        for w in worst:
            print("    ", w)
    else:
        print("  (none found — the +GAP trivial-split trap did NOT realise here)")
    # also report the maximum single one-edge ρ₊ value reached (how deep a single
    # discrete-log jump goes) — the mechanism enabling the trap.
    maxjump = 0
    for s in states:
        j, c = s.j, s.c
        M = eng.modulus(j)
        for a in ADMISSIBLE:
            t = TAU[a]
            y = (eng.inv_pow2(t, j) * c) % M
            if y % 9 == a:
                maxjump = max(maxjump, nu3(y - 1))
    print(f"  max single one-edge ν₃(v.c−1) (deepest 1-step ρ₊ reached): {maxjump}")
    print()


if __name__ == "__main__":
    scan(m=1, Q=12, GAP=22)
    scan(m=1, Q=15, GAP=22)
    # smaller gap to show monotone behaviour
    scan(m=1, Q=12, GAP=10)
