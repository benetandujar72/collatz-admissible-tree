"""
D3 -- HARDEST BREAK ATTEMPT against the adequacy verdict.

The verdict says route-A (per-block induction) is DEAD. The most promising way to
BREAK that is to find a CORRECTED inductive obligation that (a) still yields the
(m+1)-barrier via barrier_step_of_split, (b) is NOT refuted by the trap witness,
(c) is NOT circular (provable without assuming kappa1>=m on the deep prefix).

barrier_step_of_split consumes KappaPathSplit m Q, which is EXISTENTIAL in mid:
  forall (m+1)-goal-path,  EXISTS mid: prefix kappa1 >= m  AND  suffix kappa2 >= 1.
It does NOT require m-precision in its OUTPUT, and does NOT require a UNIVERSAL
prefix floor. So the natural "corrected obligation" is KappaPathSplit ITSELF
(drop the m-precision that BlockBoundaryExists added).

QUESTION 1 (refutation): is KappaPathSplit refuted by the trap witness?
QUESTION 2 (provability/circularity): can KappaPathSplit be proven for the witness
  WITHOUT the IH (which needs m-precision)? The only mid that works is non-m-precise
  (mid=trap or an interior ladder vertex). For THAT mid, what proves kappa1>=m?

We enumerate, on the witness, ALL splits (mid = each vertex) and record:
  - is mid m-precise? (=> IH can fire on prefix => kappa1>=m provable BY IH)
  - prefix kappa1, suffix kappa2
  - does the split satisfy KappaPathSplit's requirement (k1>=m, k2>=1)?
  - for the satisfying splits, is mid m-precise (IH available) or not (IH unavailable)?

If EVERY satisfying split has a NON-m-precise mid, then KappaPathSplit holds on the
witness but its proof CANNOT route through the IH -- confirming the verdict's
"true but inductively unprovable" diagnosis. If SOME satisfying split has an
m-precise mid with k2>=1, the verdict's Lemma B would be WRONG.
"""

import json


def two_pow_mod9(e):
    return pow(2, e % 6, 9)


def build_path(m, W):
    """Explicit witness: dlog-space ladder from W (class7) down to 2 (class4=trap),
    then deep edge to goal c=1. Returns vertices with real residues mod M and per-edge kappa."""
    R = 22 * (m + 1) + 2
    M = 3 ** (R + 1)
    aS202 = 1 + 3 ** 22
    start_c = aS202 % M
    assert W % 6 == 4
    # dlog descent
    ds = []
    d = W
    while True:
        ds.append(d)
        if d == 2:
            break
        d = d - (2 if d % 6 == 4 else 4)
    verts = [(0, start_c, None, "start")]
    for idx, dd in enumerate(ds):
        c = pow(2, dd, M)
        k = 0 if idx == 0 else 1           # entry zero-edge k=0, ladder one-edges k=+1
        verts.append((1, c, k, f"d={dd}"))
    verts.append((1, 1, 1, "goal"))         # deep one-edge k=+1
    return verts, M


def m_precise(c, j, m, M):
    mod = 3 ** (22 * m + 2 + j)
    return (c % mod) == (1 % mod)


def enumerate_splits(m, W):
    verts, M = build_path(m, W)
    n = len(verts)
    goal_idx = n - 1
    rows = []
    satisfying = []
    for i in range(1, n):  # mid = verts[i]; prefix = 0..i, suffix = i..goal
        prefix_k = sum(verts[t][2] for t in range(1, i + 1))         # edges into 1..i
        suffix_k = sum(verts[t][2] for t in range(i + 1, n))         # edges into i+1..goal
        mp = m_precise(verts[i][1], verts[i][0], m, M)
        sat = (prefix_k >= m and suffix_k >= 1)
        rows.append(dict(mid=verts[i][3], mod9=verts[i][1] % 9, mprecise=mp,
                         prefix_k=prefix_k, suffix_k=suffix_k, satisfies_KPS=sat))
        if sat:
            satisfying.append((i, mp))
    # diagnostics
    sat_with_mprecise_mid = [i for (i, mp) in satisfying if mp]
    sat_with_nonmprecise_mid = [i for (i, mp) in satisfying if not mp]
    return dict(
        m=m, W=W, ladder_len=len([v for v in verts if v[3].startswith("d=")]),
        total_kappa=sum(v[2] for v in verts if v[2] is not None),
        KPS_satisfiable=(len(satisfying) > 0),
        any_satisfying_split_has_mprecise_mid=(len(sat_with_mprecise_mid) > 0),
        all_satisfying_splits_nonmprecise=(len(satisfying) > 0 and len(sat_with_mprecise_mid) == 0),
        num_satisfying=len(satisfying),
        splits=rows,
    )


if __name__ == "__main__":
    for (m, W) in [(1, 22), (2, 22), (3, 22), (3, 100), (5, 100)]:
        r = enumerate_splits(m, W)
        # compact print: the headline booleans + the satisfying splits only
        head = {k: r[k] for k in
                ("m", "W", "ladder_len", "total_kappa", "KPS_satisfiable",
                 "any_satisfying_split_has_mprecise_mid",
                 "all_satisfying_splits_nonmprecise", "num_satisfying")}
        print(json.dumps(head, indent=2))
        sat_rows = [s for s in r["splits"] if s["satisfies_KPS"]]
        print("  satisfying splits (the only ones barrier_step_of_split could use):")
        for s in sat_rows:
            print("   ", s)
        print("-" * 64)
