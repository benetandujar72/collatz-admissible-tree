"""
SYNTHESIZER verification of the decisive claims.

F4 (D1 headline, g-INDEPENDENT): KappaPathSplit m Q  <=>  barrier_bounded (m+1) Q.
  Forward (split => sum >= m+1) is barrier_step_of_split (proven in Lean).
  Backward (barrier => split) is the OPEN half; D1 claims it is the discrete-IVT
  on unit-step partial sums of a {-1,0,+1} kappa-sequence -> AUTOMATIC, hence the
  step hypothesis IS its own conclusion -> the induction sheds no content.

We test BACKWARD rigorously:
  Claim: for any kappa-sequence over {-1,0,+1} with total K >= m+1 (m>=1), there is
  an interior cut index p (1 <= p <= L-1) with prefix-sum = m exactly and suffix-sum
  = K-m >= 1, AND both prefix and suffix are nonempty (vs1 != [], vs2 != []).
  The "first index where partial sum hits m" realizes it.

Also: the WPath by-index split (inverse of WPath_concat) is elementary; we model
WPath as a list of (edge-weight) and confirm prefix/suffix reconstruct.

Witness sanity: confirm a {-1,0,+1} kappa-walk modelling the trap witness
([entry 0][ladder +1 x L][deep +1], total = L+1) admits a split with k1>=m,k2>=1
for every m with L+1 >= m+1 -> NOT refuted (it is satisfiable; just every
satisfying cut is at a non-m-precise vertex, which the IH cannot bind).
"""
import itertools, random

def first_hit_split(kappas, m):
    """Return (p, k1, k2) where p = first index with prefix-sum == m, or None.
    Cut places first p edges in prefix (vs1 = targets of edges 0..p-1),
    remaining in suffix. Interior cut requires 1 <= p <= L-1."""
    s = 0
    for p in range(1, len(kappas) + 1):
        s += kappas[p - 1]
        if s == m:
            k1 = m
            k2 = sum(kappas) - m
            return (p, k1, k2)
    return None

def split_exists_any(kappas, m):
    """Does ANY interior cut give k1>=m and k2>=1?"""
    K = sum(kappas)
    s = 0
    for p in range(1, len(kappas)):  # interior: 1..L-1
        s += kappas[p - 1]
        if s >= m and (K - s) >= 1:
            return True
    return False

# ---- TEST 1: exhaustive small walks, backward direction (first-hit cut) ----
viol_firsthit = 0
viol_anyexists = 0
total = 0
for L in range(1, 13):
    for kappas in itertools.product((-1, 0, 1), repeat=L):
        for m in (1, 2, 3):
            K = sum(kappas)
            if K >= m + 1:
                total += 1
                # D1's canonical first-hit cut must exist and be interior with k2>=1
                r = first_hit_split(list(kappas), m)
                if r is None:
                    viol_firsthit += 1
                else:
                    p, k1, k2 = r
                    # interior (both nonempty) and bounds
                    if not (1 <= p <= L - 1 and k1 == m and k2 >= 1):
                        viol_firsthit += 1
                # the weaker "some cut exists" (== bare KappaPathSplit satisfiability)
                if not split_exists_any(list(kappas), m):
                    viol_anyexists += 1

print(f"[T1 exhaustive] walks with K>=m+1 tested: {total}")
print(f"[T1] first-hit-cut violations (D1 canonical split fails): {viol_firsthit}")
print(f"[T1] any-interior-cut violations (KappaPathSplit unsatisfiable): {viol_anyexists}")

# ---- TEST 2: long random adversarial walks ----
random.seed(20260601)
viol2 = 0
n2 = 0
for _ in range(300000):
    L = random.randint(2, 400)
    kappas = [random.choice((-1, 0, 1)) for _ in range(L)]
    m = random.randint(1, 8)
    if sum(kappas) >= m + 1:
        n2 += 1
        r = first_hit_split(kappas, m)
        ok = r is not None and 1 <= r[0] <= L - 1 and r[1] == m and r[2] >= 1
        if not ok:
            viol2 += 1
print(f"[T2 random long] walks with K>=m+1: {n2}, first-hit-cut violations: {viol2}")

# ---- TEST 3: the converse (a split forces K>=m+1) -- sanity, always true by additivity
# (k1>=m, k2>=1, K=k1+k2 => K>=m+1). Nothing to brute; it's arithmetic.

# ---- TEST 4: WPath by-index split soundness (model) ----
# Model a WPath as ordered edge weights; prefix = first p, suffix = rest.
# Reconstruct: sum(prefix)+sum(suffix)==total and concatenation of interiors==full.
viol4 = 0
for _ in range(20000):
    L = random.randint(0, 30)
    weights = [random.choice((-1, 0, 1)) for _ in range(L)]
    interiors = [f"v{i}" for i in range(L)]  # WPath interior = edge targets
    for p in range(0, L + 1):
        pre_w, suf_w = sum(weights[:p]), sum(weights[p:])
        pre_i, suf_i = interiors[:p], interiors[p:]
        if pre_w + suf_w != sum(weights):
            viol4 += 1
        if pre_i + suf_i != interiors:
            viol4 += 1
print(f"[T4 WPath by-index split] reconstruction violations: {viol4}")

# ---- TEST 5: trap-witness kappa-walk is SATISFIABLE (not refuted) for all m ----
# witness kappa-seq: entry zero (0), ladder of L ones (+1 each), deep one (+1).
# total = L+1. For every m with L+1 >= m+1 i.e. L>=m, a split with k1>=m,k2>=1 exists.
viol5 = 0
checked5 = 0
for L in range(1, 50):
    kappas = [0] + [1] * L + [1]   # entry zero, L ladder ones, deep one ; total = L+1
    K = sum(kappas)
    for m in range(1, L + 1):       # K = L+1 >= m+1  <=>  m <= L
        checked5 += 1
        if not split_exists_any(kappas, m):
            viol5 += 1
print(f"[T5 trap-witness] (m,L) satisfiable checks: {checked5}, NOT-satisfiable: {viol5}")

print()
print("VERDICT inputs:")
print(f"  Backward direction (barrier=>split) FAILS in: {viol_firsthit + viol2} cases  (0 => RIGOROUS)")
print(f"  => F4 circularity {'CONFIRMED' if viol_firsthit+viol2 == 0 and viol_anyexists==0 else 'BROKEN'}")
print(f"  Trap witness refutes bare KappaPathSplit: {'YES' if viol5>0 else 'NO (satisfiable, not refuted)'}")
