"""
ADVERSARIAL independent verification of the B2 empty-suffix witness.

I do NOT reuse their succ(). I rebuild the inverse-edge relation from the VERIFIED FACTS
verbatim and check the reconstructed witness edge-by-edge against the FORWARD congruence
   one-edge: v.c ≡ 2^τ(v'.c) · v'.c   (mod 3^(B+j))      [same j], v'.c%9∈X, τ=tau(v'.c%9)
   zero-edge: 3·v.c + 1 ≡ 2^τ(v'.c) · v'.c (mod 3^(B+j+1))  [j -> j+1]
GOAL: c ≡ 1 mod 3^(B+j).  m-precise (forbidden): c ≡ 1 mod 3^(R0+j).

Then I independently BFS the clean graph and confirm:
  (A) a clean working-goal exists (mid=goal first-m-precise), interior strictly non-m-precise,
  (B) EVERY reconstructed edge satisfies the FORWARD congruence (not just the inverse I used to walk),
  (C) the penultimate vertex is the deep trap c≡4, final edge one-edge with tau=2,
  (D) report total kappa and whether ANY shorter clean goal exists with mid!=goal.
"""
from collections import deque

X = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}


def tau(cp):           # tau as a function of the TARGET residue mod 9
    return TAU[cp % 9]


def forward_one_ok(c, cp, j, B):
    """Check the FORWARD inverse-graph one-edge congruence v.c ≡ 2^τ·v'.c mod 3^(B+j)."""
    M = 3 ** (B + j)
    if cp % 9 not in X:
        return False
    t = tau(cp)
    return (c - (pow(2, t, M) * cp)) % M == 0


def forward_zero_ok(c, cp, j, B):
    """Check FORWARD zero-edge 3c+1 ≡ 2^τ·v'.c mod 3^(B+j+1) (source j -> target j+1)."""
    M1 = 3 ** (B + j + 1)
    if cp % 9 not in X:
        return False
    t = tau(cp)
    return ((3 * c + 1) - (pow(2, t, M1) * cp)) % M1 == 0


def inv_one_succ(j, c, B):
    """Inverse one-edge successors c' = 2^{-t} c mod 3^(B+j), keep iff c'%9 == alpha (so tau consistent)."""
    out = []
    M = 3 ** (B + j)
    for a in X:
        t = TAU[a]
        inv = pow(pow(2, t, M), -1, M)
        cp = (inv * c) % M
        if cp % 9 == a:
            out.append((j, cp, 'one', t, +1))
    return out


def inv_zero_succ(j, c, B):
    """Inverse zero-edge successors: target j+1, c' with 3c+1 ≡ 2^t c' mod 3^(B+j+1), c'%9==alpha."""
    out = []
    M1 = 3 ** (B + j + 1)
    val = (3 * c + 1) % M1
    for a in X:
        t = TAU[a]
        inv = pow(pow(2, t, M1), -1, M1)
        cp = (inv * val) % M1
        if cp % 9 == a:
            out.append((j + 1, cp, 'zero', t, -1 if t == 1 else 0))
    return out


def succ(j, c, B, Q):
    out = inv_one_succ(j, c, B)
    if j < Q:
        out += inv_zero_succ(j, c, B)
    return out


def analyse(w, Q):
    R0, B = w + 2, 2 * w + 2
    start = (0, (1 + 3 ** w) % 3 ** B)
    forb = lambda s: s[1] % 3 ** (R0 + s[0]) == 1
    isg  = lambda s: s[1] % 3 ** (B + s[0]) == 1
    ist  = lambda s: s[1] % 3 ** (B + s[0]) == 4
    assert not forb(start), "start must NOT be m-precise (else artifact)"

    # clean BFS: forbidden vertices are sinks; stop at FIRST working-goal found
    par = {start: (None, None, None, 0)}
    q = deque([start]); goal = None
    while q:
        s = q.popleft()
        if isg(s) and s[0] >= 1:
            goal = s; break
        if s != start and forb(s):
            continue
        for (jp, cp, kind, t, ka) in succ(*s, B, Q):
            sp = (jp, cp)
            if sp not in par:
                par[sp] = (s, kind, t, ka); q.append(sp)
    if goal is None:
        return {"w": w, "Q": Q, "clean_goal": False}

    # reconstruct
    seq = []; cur = goal
    while cur is not None:
        prev, kind, t, ka = par[cur]
        seq.append((cur, kind, t, ka)); cur = prev
    seq = list(reversed(seq))   # seq[0] = start (kind None)

    # === independent FORWARD-congruence audit of EVERY edge ===
    edge_ok = True
    bad = None
    for i in range(1, len(seq)):
        c_src = seq[i - 1][0][1]; j_src = seq[i - 1][0][0]
        c_tgt = seq[i][0][1]
        kind = seq[i][1]; t_used = seq[i][2]
        if kind == 'one':
            ok = forward_one_ok(c_src, c_tgt, j_src, B) and seq[i][0][0] == j_src
            ok = ok and (tau(c_tgt) == t_used)
        else:
            ok = forward_zero_ok(c_src, c_tgt, j_src, B) and seq[i][0][0] == j_src + 1
            ok = ok and (tau(c_tgt) == t_used)
        if not ok:
            edge_ok = False; bad = (i, seq[i - 1][0], seq[i][0], kind, t_used); break

    n = len(seq)
    interior_clean = all(not forb(seq[i][0]) for i in range(n - 1))
    # also: is the goal (last) the UNIQUE m-precise vertex on the whole path?
    mprec_positions = [i for i in range(n) if forb(seq[i][0])]
    goal_is_first_mprec = (mprec_positions == [n - 1])
    penult = seq[-2][0]
    final_edge = seq[-1][1:]
    kappa_total = sum(s[3] for s in seq)

    return {
        "w": w, "Q": Q, "B": B, "R0": R0, "clean_goal": True,
        "n_edges": n - 1, "start": start, "goal": goal,
        "FORWARD_edges_all_valid": edge_ok, "first_bad_edge": bad,
        "interior_all_non_mprecise": interior_clean,
        "goal_is_unique_mprecise_on_path": goal_is_first_mprec,
        "mprec_positions": mprec_positions, "path_n_vertices": n,
        "penult_is_trap_c4": ist(penult),
        "final_edge_kind_tau_kappa": final_edge,
        "kappa_total": kappa_total,
    }


if __name__ == "__main__":
    print("ADVERSARIAL re-verification: rebuild edges from VERIFIED FACTS, audit FORWARD congruence.\n")
    for (w, Q) in [(2, 1), (2, 2), (3, 1), (3, 2), (4, 1)]:
        r = analyse(w, Q)
        print(f"=== w={w} Q={Q} ===")
        for kk in ["clean_goal", "n_edges", "FORWARD_edges_all_valid", "first_bad_edge",
                   "interior_all_non_mprecise", "goal_is_unique_mprecise_on_path",
                   "penult_is_trap_c4", "final_edge_kind_tau_kappa", "kappa_total", "goal"]:
            if kk in r:
                print(f"   {kk}: {r[kk]}")
        print()
