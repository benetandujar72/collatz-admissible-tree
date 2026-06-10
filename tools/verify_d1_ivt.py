"""
INDEPENDENT adversarial verification of D1's F4 (circularity via discrete-IVT).

We do NOT trust the D1 author's analog. We test the PURE combinatorial claim that
underlies kappaPathSplit_iff_barrier_succ, which is g-independent:

  CLAIM (F4 forward): For an edge-kappa sequence e_1..e_L with each e_i in {-1,0,+1}
  and total K = sum e_i, IF K >= m+1 (m>=1) THEN there is an interior index p
  (1<=p<=L-1) such that the prefix sum S_p = sum_{i<=p} e_i satisfies
      S_p >= m  AND  K - S_p >= 1   (i.e. prefix kappa1>=m, suffix kappa2>=1).
  Hence KappaPathSplit holds for this path.

  CONVERSE: a split with k1>=m, k2>=1 forces K = k1+k2 >= m+1.

If BOTH hold for EVERY {-1,0,+1} walk, then KappaPathSplit m Q <=> barrier(m+1) Q
PATHWISE, hence the predicates are equivalent and barrier_step_of_split is the trivial
half. That is the circularity verdict.

CRITICAL SUBTLETIES we attack:
 (A) The IVT must give an INTERIOR cut. If the only place S hits [m, K-1] is at the
     very last node (p=L) or only at p=0, the split is degenerate (empty suffix/prefix)
     and KappaPathSplit's vs2 != [] requirement (k2>=1) could fail. The author claims
     p interior always exists. We brute-force search for a counterexample walk.
 (B) Exactness: does WPath_first_witness_split at predicate "S reaches m" give k1=m
     EXACTLY? We check whether 'first index where S_p = m' is well-defined and interior.
     Note S can OVERSHOOT past m only by unit steps, so it must EQUAL m at first crossing
     from below -- but it could first reach m, dip, and the SUFFIX from that point could
     still be >=1. We verify the precise statement the Lean target needs.
 (C) Re-run the ACTUAL trap witness kappa-sequence against the obligation.

We exhaustively enumerate ALL walks of length up to L_MAX over alphabet {-1,0,+1}
with total K in [m+1 .. ], and also random long walks, looking for ANY violation.
"""
from __future__ import annotations
import itertools, random

def has_interior_split(es, m):
    """Return (ok, p, k1, k2) : does there exist interior cut p (1<=p<=L-1) with
       prefix-sum>=m and suffix-sum>=1?  We mirror EXACTLY what KappaPathSplit asks:
       the path vs = vs1 ++ vs2 with both legs being genuine WPaths. In WPath terms an
       interior cut at index p means vs1 = first p targets, vs2 = remaining; the split
       point 'mid' is the target of edge p. BOTH legs may be empty in WPath_first_witness_
       split, but KappaPathSplit additionally needs k1>=m AND k2>=1. We require a cut
       0<=p<=L (p=0 -> empty prefix mid=start; p=L -> empty suffix mid=goal) such that
       k1=S_p>=m and k2=K-S_p>=1. Existence of ANY such p (incl. p that makes mid=start
       or interior) suffices for KappaPathSplit because KappaPathSplit does NOT require
       mid to be distinct from endpoints -- it only needs the two WPaths to exist."""
    L = len(es)
    K = sum(es)
    S = 0
    prefix = [0]
    for e in es:
        S += e
        prefix.append(S)
    # p ranges over 0..L (cut after p edges). k1=prefix[p], k2=K-prefix[p].
    for p in range(0, L + 1):
        k1 = prefix[p]
        k2 = K - k1
        if k1 >= m and k2 >= 1:
            return True, p, k1, k2
    return False, None, None, None

def exact_first_m_cut(es, m):
    """The Lean-target cut: FIRST index p where prefix-sum reaches m (from below, unit
       steps => equals m exactly). Returns (p, k1, k2, interior?) or None if never reaches m.
       This is the cut WPath_first_witness_split would produce at predicate
       P(node) := (prefix-sum at node) >= m  (equivalently = m at first hit)."""
    S = 0
    prefix = [0]
    for e in es:
        S += e
        prefix.append(S)
    K = prefix[-1]
    for p in range(0, len(prefix)):
        if prefix[p] >= m:
            k1 = prefix[p]; k2 = K - k1
            # interior in the WPath sense relevant to k2>=1: we need k2>=1
            return p, k1, k2, (k2 >= 1)
    return None

def brute_force(L_max=14, m_values=(1,2,3)):
    print(f"== BRUTE FORCE: all walks length<={L_max} over {{-1,0,+1}}, m in {m_values} ==")
    viol_split = 0
    viol_exact = 0
    total = 0
    worst = []
    for m in m_values:
        for L in range(1, L_max + 1):
            for es in itertools.product((-1, 0, 1), repeat=L):
                K = sum(es)
                if K < m + 1:
                    continue
                total += 1
                ok, p, k1, k2 = has_interior_split(es, m)
                if not ok:
                    viol_split += 1
                    if len(worst) < 20:
                        worst.append(("NO-SPLIT", m, es, K))
                # exactness of the first-m cut
                ex = exact_first_m_cut(es, m)
                if ex is None or not ex[3]:
                    # first-m cut fails to leave a positive suffix => the EXACT Lean cut
                    # would be degenerate. Does SOME OTHER cut still work? (has_interior_split)
                    if not ok:
                        pass
                    else:
                        # the generic split exists but the *first-m* cut is degenerate.
                        # This matters: the Lean proof must pick a cut that works.
                        viol_exact += 1
                        if len([w for w in worst if w[0]=="FIRSTM-DEGEN"]) < 10:
                            worst.append(("FIRSTM-DEGEN", m, es, K, ex))
    print(f"  walks with K>=m+1 tested: {total}")
    print(f"  walks with NO valid (k1>=m,k2>=1) split AT ALL: {viol_split}")
    print(f"  walks where the FIRST-m cut is degenerate (k2=0) but some split exists: {viol_exact}")
    for w in worst:
        print("   ", w)
    return viol_split, viol_exact

def random_long(trials=300000, Lmin=20, Lmax=400, m_values=(1,2,5,10)):
    print(f"== RANDOM LONG: {trials} walks, length [{Lmin},{Lmax}], m in {m_values} ==")
    rng = random.Random(20260601)
    viol = 0; tested = 0; firstm_degen = 0
    for _ in range(trials):
        m = rng.choice(m_values)
        L = rng.randint(Lmin, Lmax)
        # bias toward walks that satisfy K>=m+1
        es = [rng.choice((-1, 0, 1)) for _ in range(L)]
        K = sum(es)
        if K < m + 1:
            continue
        tested += 1
        ok, *_ = has_interior_split(es, m)
        if not ok:
            viol += 1
            print("   VIOLATION", m, K, es[:30])
        ex = exact_first_m_cut(es, m)
        if ex is None or not ex[3]:
            firstm_degen += 1
    print(f"  tested {tested}; NO-split violations: {viol}; first-m-cut degenerate: {firstm_degen}")
    return viol

def trap_witness():
    """The ACTUAL Lean trap witness kappa-sequence (LadderExists.lean):
       entry zero-edge (k=0), ladder of one-edges (each +1, length L_lad), deep one-edge (+1).
       Total K = L_lad + 1. We test the obligation for several L_lad (the real one ~3e21).
       Also test D1's CHEAP case-(b) route from d1_dissect (k=2=M at M=2): the sequence
       [-1, 0, +1, +1, 0, 0, +1] (kappas in execution order)."""
    print("== TRAP WITNESS against the proposed obligation ==")
    # Lean witness: entry(0) + ladder(+1 * L) + deep(+1).  m = M-1 where M=m+1 is the cylinder.
    # For the astronomical real ladder we use the CLOSED FORM (no list build):
    # es = [0] + [1]*L + [1]; prefix sums are 0,0,1,2,...,L,L+1; K=L+1.
    # First index where prefix>=m: after the entry-0 and m one-edges => cut at p=m+1 (0-based over
    # the L+2 edges), giving k1=m, k2=K-m=L+1-m. Interior & k2>=1 iff L+1-m>=1 iff L>=m.
    for L_lad in (1, 5, 100, 3_000_000_000_000_000_000_000):
        K = L_lad + 1
        for m in (1, 2):
            # closed-form: split exists iff K>=m+1; first-m cut leaves k2 = K-m
            split_exists = (K >= m + 1)
            k1 = m if split_exists else None
            k2 = (K - m) if split_exists else None
            firstm_ok = split_exists and (K - m >= 1)
            print(f"  Lean-witness L_lad={L_lad:>25} K={K} m={m}: split_exists={split_exists} "
                  f"(k1={k1},k2={k2}); first-m-cut interior_ok={firstm_ok}")
    # D1 cheap case-(b) route at M=2 => m=1: kappa seq from d1_dissect.py
    es_cheap = [-1, 0, 1, 1, 0, 0, 1]   # total = 2
    for m in (1,):
        ok, p, k1, k2 = has_interior_split(es_cheap, m)
        ex = exact_first_m_cut(es_cheap, m)
        print(f"  D1-cheap-route es={es_cheap} K={sum(es_cheap)} m={m}: split_exists={ok} "
              f"(k1={k1},k2={k2}); first-m-cut={ex}")
    # ADVERSARIAL: the dangerous case for KappaPathSplit is K = m EXACTLY (floor). Then
    # k1>=m and k2>=1 needs k1+k2>=m+1>m=K -> IMPOSSIBLE. So a floor path with K=m has NO
    # split. Does KappaPathSplit then FAIL? It would -- BUT barrier(m+1) says K>=m+1, so a
    # K=m path to an (m+1)-goal cannot exist if the barrier holds. The equivalence is only
    # claimed for paths with K>=m+1. Show the K=m degeneracy explicitly:
    print("  -- degeneracy probe: a path with K=m has NO (k1>=m,k2>=1) split --")
    for m in (1,2,3):
        es = [1]*m  # K=m exactly
        ok, *_ = has_interior_split(es, m)
        print(f"     m={m}, es={es}, K={sum(es)}: split_exists={ok}  "
              f"(expected False; consistent: such a path violates barrier(m+1))")

if __name__ == "__main__":
    v1, v2 = brute_force(L_max=14, m_values=(1,2,3))
    print()
    v3 = random_long()
    print()
    trap_witness()
    print()
    print("VERDICT INPUTS:")
    print(f"  brute-force no-split violations: {v1}")
    print(f"  brute-force first-m-cut-degenerate (but split exists elsewhere): {v2}")
    print(f"  random-long no-split violations: {v3}")
    print("  If no-split violations == 0 for ALL K>=m+1 walks, then barrier(m+1)=>KappaPathSplit")
    print("  holds combinatorially (F4 forward). Converse (split=>K>=m+1) is arithmetic-trivial.")
