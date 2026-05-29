"""
structure_probe.py — verify the 3-adic transition laws underlying the
discrete-log / lifting-the-exponent attack on the κ-precise barrier.

Claimed laws (for the inverse cylinder graph at base R, modulus M=3^(R+j)):
  (1) one-edge   c -> c'=2^{-τ}c:   ρ₊(c') = ν₃(c - 2^τ)         (capped at r)
  (2) zero τ=2:                     ρ₊(c') = ρ₊(c) + 1
  (3) zero τ∈{1,3}:                 ρ₊(c') = 0
where ρ₊(x, r) = min(ν₃(x-1), r),  τ = τ(c') determined by c' mod 9.

We enumerate the reachable region (S202 engine BFS, cost-pruned), classify
every actual edge, and CHECK each law. Any violation is printed.

Also: confirm the discrete-log lower bound for the start aS202 = 1+3^(R-2).
"""
from __future__ import annotations
from collections import deque
from s202_engine import S202Engine, State, ADMISSIBLE, TAU


def nu3(x: int) -> int:
    """3-adic valuation of a nonzero integer; nu3(0) = large."""
    if x == 0:
        return 10**9
    x = abs(x)
    k = 0
    while x % 3 == 0:
        x //= 3
        k += 1
    return k


def rho_plus(c: int, r: int) -> int:
    return min(nu3(c - 1), r)


def reachable_region(eng: S202Engine, T: int, max_states: int):
    """Cost-pruned (optimistic) reachable states from start, as in S216."""
    dist = {eng.start: 0}
    q = deque([eng.start])
    seen = {eng.start}
    while q:
        s = q.popleft()
        d = dist[s]
        # optimistic cut on ACTUAL defect weights
        if d - (eng.Q - s.j) >= T:
            continue
        for (t, w) in eng.outgoing_edges(s):
            nd = d + w
            if nd - (eng.Q - t.j) >= T:
                continue
            if t not in seen and len(seen) < max_states:
                seen.add(t); dist[t] = nd; q.append(t)
            elif t in seen and nd < dist[t]:
                dist[t] = nd; q.append(t)
    return list(seen)


def check_laws(m: int, Q: int, T: int = 6, max_states: int = 60000):
    eng = S202Engine(m=m, Q=Q)
    R = eng.R
    states = reachable_region(eng, T, max_states)
    n_one = n_z2 = n_z13 = n_z4 = 0
    bad1 = bad2 = bad3 = 0
    ex1 = []
    for s in states:
        j, c = s.j, s.c
        r = R + j
        M = 3 ** r
        # one-edges
        for alpha in ADMISSIBLE:
            t = TAU[alpha]
            y = (eng.inv_pow2(t, j) * c) % M
            if y % 9 == alpha:
                n_one += 1
                lhs = rho_plus(y, r)
                rhs = min(nu3((c - 2**t) % M), r)   # nu3 of (c - 2^τ) mod 3^r
                if lhs != rhs:
                    bad1 += 1
                    if len(ex1) < 4:
                        ex1.append((j, c, y, t, lhs, rhs))
        # zero-edges
        if j < Q:
            M1 = 3 ** (r + 1)
            val = (3 * c + 1) % M1
            for alpha in ADMISSIBLE:
                t = TAU[alpha]
                y = (eng.inv_pow2(t, j + 1) * val) % M1
                if y % 9 == alpha:
                    lhs = rho_plus(y, r + 1)
                    if t == 2:
                        n_z2 += 1
                        if lhs != rho_plus(c, r) + 1:
                            bad2 += 1
                    elif t in (1, 3):
                        n_z13 += 1
                        if lhs != 0:
                            bad3 += 1
                    else:  # t == 4
                        n_z4 += 1
    print(f"=== m={m}, Q={Q}, T={T}: {len(states)} states ===")
    print(f"  one-edges checked      : {n_one:6d}   law(1) ρ₊(c')=ν₃(c-2^τ) violations: {bad1}")
    print(f"  zero τ=2 edges checked  : {n_z2:6d}   law(2) ρ₊(c')=ρ₊(c)+1   violations: {bad2}")
    print(f"  zero τ∈1,3 edges checked: {n_z13:6d}   law(3) ρ₊(c')=0          violations: {bad3}")
    print(f"  zero τ=4 edges (no simple law): {n_z4}")
    if ex1:
        print(f"  law(1) counterexamples: {ex1}")


def dlog_lower_bound(m: int):
    """Confirm the LTE/discrete-log structure for the start aS202 mod 3^R."""
    R = 22 * m + 2
    M = 3 ** R
    aS202 = (1 + 3 ** 22) % M if m == 1 else None
    eng = S202Engine(m=m, Q=0)
    c0 = eng.target
    print(f"=== discrete-log structure, m={m}, R={R} ===")
    print(f"  c0 = aS202 mod 3^{R};  ρ₊(c0) = ν₃(c0-1) = {nu3(c0 - 1)}  (cap {R})")
    # need 2^S ≡ c0 (mod 3^R); for m=1 c0=1+3^22 so need ν₃(2^S - 1) = 22.
    # LTE: ν₃(2^S-1) = 1 + ν₃(S/2) for S even.  => ν₃(S)=21 => S = 2·3^21·u.
    if m == 1:
        S_min = 2 * 3 ** 21
        print(f"  need ν₃(2^S-1)=22 ⟹ ν₃(S)=21 ⟹ S ≥ 2·3^21 = {S_min}")
        # verify: 2^(2·3^21) mod 3^24 has the right ν₃ (use pow with modulus 3^24)
        val = pow(2, S_min, M)
        print(f"  check ν₃(2^(2·3^21) - 1) mod 3^24 = {nu3((val - 1) % M)} (want ≥ 22)")
        print(f"  ⟹ pure-one-edge n_one ≥ S/4 ≈ {S_min // 4} ≈ 3^21/2  (astronomically ≫ m=1)")


if __name__ == "__main__":
    for (m, Q) in [(1, 3), (1, 5)]:
        check_laws(m, Q)
        print()
    dlog_lower_bound(1)
