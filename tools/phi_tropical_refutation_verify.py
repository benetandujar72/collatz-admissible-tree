"""
phi_tropical_refutation_verify.py — independent check of the S241 tropical refutation.

CLAIM (from phi_quotient_refuter.py, m=1, Q=5, R=24): no function of the tropical
features  F(j,c) = (j, (min(nu3((c - 2^s*a) mod 3^(R+j)), R+j))_{a in {1,4,a*}, s=0..5})
can be a valid slice potential for S202_kappa_precise_barrier_bounded_from_potential,
because there exist
  u = (4, 2343282560492)   with a REAL kappa-path  InvStart -> u  of total cost -2,
  v = (4, 5)               with a REAL kappa-path  v -> goal      of total cost +1,
and F(u) = F(v).  Then for any tropical-feature Phi:
  1 = m <= Phi(start) <= (-2) + Phi(u) = (-2) + Phi(v) <= (-2) + 1 + Phi(goal) <= -1.
Contradiction.

This file re-derives everything with INDEPENDENT inline arithmetic (no engine import
for the verification step): edge legality, kappa weights, feature equality.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")

R = 24
Q = 5
M0 = 3 ** R
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}
ADM = (1, 2, 4, 5, 7, 8)
SHIFTS = (0, 1, 2, 3, 4, 5)

# start residue: aS202 mod 3^R  (B202 / (2^43 - 3^22) mod 3^R) — recomputed inline
B202, A202, Q202 = 919_447_060_349, 43, 22
START = (B202 * pow((2 ** A202 - 3 ** Q202) % M0, -1, M0)) % M0
ASTAR = START  # a202_mod(R) is the same quantity


def v3_capped(x, M, cap):
    x %= M
    if x == 0:
        return cap
    v = 0
    while x % 3 == 0 and v < cap:
        x //= 3
        v += 1
    return v


def trop_features(j, c):
    M = 3 ** (R + j)
    cap = R + j
    out = [j]
    for a in (1, 4, ASTAR):
        for s in SHIFTS:
            out.append(v3_capped(c - pow(2, s, M) * a, M, cap))
    return tuple(out)


def check_edge(j, c, j2, c2):
    """Independent legality + kappa of a claimed edge (j,c) -> (j2,c2). Returns kappa."""
    if j2 == j:  # one-edge: c2 = 2^{-tau(alpha)} c with alpha = c2 % 9 admissible
        M = 3 ** (R + j)
        alpha = c2 % 9
        assert alpha in ADM, "target class not admissible"
        t = TAU[alpha]
        assert (pow(2, t, M) * c2 - c) % M == 0, "one-edge arithmetic fails"
        return 1
    elif j2 == j + 1:  # zero-edge: 2^{tau(alpha)} c2 = 3c+1 mod 3^(R+j+1)
        assert j < Q, "zero-edge beyond slice"
        M1 = 3 ** (R + j + 1)
        alpha = c2 % 9
        assert alpha in ADM, "target class not admissible"
        t = TAU[alpha]
        assert (pow(2, t, M1) * c2 - (3 * c + 1)) % M1 == 0, "zero-edge arithmetic fails"
        return -1 if t == 1 else 0
    raise AssertionError("bad levels")


def find_path_to(target, T=5, max_states=400_000):
    """Parent-tracking SPFA over the kappa graph (same optimistic cut as S216)."""
    from collections import deque
    start = (0, START)
    dist = {start: 0}
    parent = {}
    qq = deque([start])
    inq = {start}
    while qq:
        s = qq.popleft()
        inq.discard(s)
        j, c = s
        d = dist[s]
        if d - (Q - j) >= T:
            continue
        M = 3 ** (R + j)
        edges = []
        for alpha in ADM:
            t = TAU[alpha]
            y = (pow(pow(2, t, M), -1, M) * c) % M
            if y % 9 == alpha:
                edges.append(((j, y), 1))
        if j < Q:
            M1 = 3 ** (R + j + 1)
            val = (3 * c + 1) % M1
            for alpha in ADM:
                t = TAU[alpha]
                y = (pow(pow(2, t, M1), -1, M1) * val) % M1
                if y % 9 == alpha:
                    edges.append(((j + 1, y), -1 if t == 1 else 0))
        for (v, w) in edges:
            nd = d + w
            if nd - (Q - v[0]) >= T:
                continue
            if nd < dist.get(v, 10 ** 9):
                dist[v] = nd
                parent[v] = s
                if v not in inq:
                    qq.append(v)
                    inq.add(v)
        if len(dist) > max_states:
            raise RuntimeError("budget")
    if target not in dist:
        raise RuntimeError("target not reached")
    path = [target]
    while path[-1] != start:
        path.append(parent[path[-1]])
    path.reverse()
    return path, dist[target]


def main():
    u = (4, 2343282560492)
    v = (4, 5)

    # 1. feature equality
    fu, fv = trop_features(*u), trop_features(*v)
    assert fu == fv, ("FEATURES DIFFER", fu, fv)
    print(f"[1] tropical features EQUAL for u={u} and v={v}:")
    print(f"    F = {fu}")

    # 2. real path start -> u with cost -2, every edge re-verified independently
    path, du = find_path_to(u)
    kappas = [check_edge(*path[i], *path[i + 1]) for i in range(len(path) - 1)]
    assert sum(kappas) == du == -2, (sum(kappas), du)
    print(f"[2] real path InvStart -> u: {len(path)-1} edges, kappas={kappas}, "
          f"total={sum(kappas)}  (each edge verified by inline modular arithmetic)")
    print(f"    path levels/j: {[p[0] for p in path]}")

    # 3. real path v -> goal with cost +1
    vpath = [(4, 5), (5, 4), (5, 1)]
    vk = [check_edge(*vpath[i], *vpath[i + 1]) for i in range(len(vpath) - 1)]
    assert sum(vk) == 1, vk
    assert vpath[-1][1] == 1 and vpath[-1][0] <= Q
    print(f"[3] real path v -> goal: {vpath} kappas={vk} total={sum(vk)}; "
          f"goal=(5,1) is c==1 at j=5<=Q")

    # 4. the contradiction
    print("[4] for ANY Phi = g(tropical features) valid on the slice j<=5 (m=1):")
    print("      1 <= Phi(start) <= -2 + Phi(u) = -2 + Phi(v) <= -2 + 1 + Phi(goal) <= -1")
    print("    CONTRADICTION — the tropical class admits NO valid slice potential. QED")


if __name__ == "__main__":
    main()
