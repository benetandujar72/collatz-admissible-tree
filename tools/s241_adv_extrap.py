"""
ADVERSARIAL stress of the w->22 extrapolation heuristic.

The B2 verdict 'device FALSE at real scale' rests on: a CLEAN goal (mid=goal, empty suffix)
keeps existing as w grows.  I probe the structural mechanism the finding claims:

  Claim: forbidden (m-precise) density = 3^-w shrinks; branching persists; so start stays
  connected to the fine goal by a clean path.

Adversarial counter-hypotheses to test:
  (H1) Maybe the clean goal exists at small w only because R0=w+2 is so close to B=2w+2 that the
       coarse band is thin in ABSOLUTE digits (B-R0=w). As w grows the ABSOLUTE thickness grows.
       Does the *number of clean-reachable m-precise leaves BEFORE the goal* explode, eventually
       (at some w) wrapping the goal so the FIRST m-precise vertex precedes it?  -> would kill it.
  (H2) Is the clean goal ALWAYS reached purely by one-edges at the FINAL j (with a single initial
       zero-edge), i.e. does it live entirely in the one-edge functional graph?  If so, the
       relevant object is: does the one-edge orbit of the start (at level B+j) pass through c=4
       (trap) -> c=1 (goal) WITHOUT passing through any c=1 mod 3^(R0+j)?  That is a pure
       fixed-j question, exactly analysable, and its w-scaling is the real predictor.

I compute, for w=2..6 (j-level resolvable), Q=1:
  * clean goal exists?  (re-confirm)
  * does the clean goal lie in the one-edge component of (the post-first-zero vertex)?
  * the one-edge orbit structure at j=1: starting from the unique post-zero vertex, follow the
    DETERMINISTIC?? one-edge.  (One-edge successors: up to 6 branches via alpha.  But from a FIXED
    source c, how many one-edge successors actually exist?)  Count branching of the one-edge graph.
  * the minimal #one-edges from start's j=1 image to the goal c=1, staying clean, vs the number of
    m-precise vertices encountered if you DON'T avoid them (to see if avoidance is forced/possible).
"""
from collections import deque

X = (1, 2, 4, 5, 7, 8)
TAU = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}


def inv2(t, M):
    return pow(pow(2, t, M), -1, M)


def one_succ(j, c, B):
    out = []
    M = 3 ** (B + j)
    for a in X:
        t = TAU[a]
        cp = (inv2(t, M) * c) % M
        if cp % 9 == a:
            out.append((j, cp, t))
    return out


def zero_succ(j, c, B):
    out = []
    M1 = 3 ** (B + j + 1)
    val = (3 * c + 1) % M1
    for a in X:
        t = TAU[a]
        cp = (inv2(t, M1) * val) % M1
        if cp % 9 == a:
            out.append((j + 1, cp, t))
    return out


def probe(w, Q=1):
    R0, B = w + 2, 2 * w + 2
    start = (0, (1 + 3 ** w) % 3 ** B)
    forb = lambda j, c: c % 3 ** (R0 + j) == 1
    isg  = lambda j, c: c % 3 ** (B + j) == 1
    ist  = lambda j, c: c % 3 ** (B + j) == 4

    # branching of one-edge graph: for a sample of vertices, count #one-successors
    # (the inverse one-edge map: how many alpha give a kept successor)
    # measure at j=1 over the whole residue space sample
    Mj1 = 3 ** (B + 1)
    branch_counts = {}
    import random
    random.seed(0)
    sample = [random.randrange(Mj1) for _ in range(2000)]
    for c in sample:
        n = len(one_succ(1, c, B))
        branch_counts[n] = branch_counts.get(n, 0) + 1

    # clean BFS, but track: (a) clean goal exists, (b) #m-precise leaves reached before goal,
    # (c) whether the goal is in the one-edge-only reachable set from the start's zero-image(s).
    par = {start: None}
    q = deque([start]); goal = None
    mprec_leaves = 0
    while q:
        s = q.popleft()
        j, c = s
        if isg(j, c) and j >= 1:
            goal = s; break
        if s != start and forb(j, c):
            mprec_leaves += 1
            continue
        for (jp, cp, t) in one_succ(j, c, B):
            if (jp, cp) not in par:
                par[(jp, cp)] = s; q.append((jp, cp))
        if j < Q:
            for (jp, cp, t) in zero_succ(j, c, B):
                if (jp, cp) not in par:
                    par[(jp, cp)] = s; q.append((jp, cp))

    # reconstruct & count zero vs one edges, and the #m-precise vertices the clean path SKIPS past
    seq = []
    if goal:
        cur = goal
        while cur is not None:
            seq.append(cur); cur = par[cur]
        seq = list(reversed(seq))
    n_zero = sum(1 for i in range(1, len(seq)) if seq[i][0] == seq[i-1][0] + 1)
    n_one  = (len(seq) - 1) - n_zero

    return {
        "w": w, "R0": R0, "B": B, "clean_goal": goal is not None, "goal": goal,
        "path_edges": len(seq) - 1, "n_one": n_one, "n_zero": n_zero,
        "mprec_leaves_before_goal": mprec_leaves,
        "one_edge_branching_hist": dict(sorted(branch_counts.items())),
        "forbidden_density_pred": f"3^-{w} = {3.0**(-w):.3e}",
    }


if __name__ == "__main__":
    print("ADVERSARIAL extrapolation stress: clean goal persistence + structural mechanism.\n")
    for w in range(2, 7):
        if 2 * w + 2 + 1 > 14:
            print(f"w={w}: SKIP (modulus too large)"); continue
        r = probe(w)
        print(f"w={w} R0={r['R0']} B={r['B']}: clean_goal={r['clean_goal']} "
              f"edges={r['path_edges']} (one={r['n_one']} zero={r['n_zero']}) "
              f"mprec_leaves_before={r['mprec_leaves_before_goal']}")
        print(f"     one-edge branching hist (n_succ:count over 2000 random c): {r['one_edge_branching_hist']}")
        print(f"     forbidden density predicted: {r['forbidden_density_pred']}")
        print()
