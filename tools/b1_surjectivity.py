"""
B1 -- Prove the per-level surjectivity is SELF-SUSTAINING and R-independent.

Claim (the engine behind 'reps at level L = all units' for every L):
  Let U_L = units mod 3^L. Suppose at level L every unit is a reachable representative
  (inductive hypothesis). The zero-edges from level L to L+1 act by:
     c (unit mod 3^L, the rep) --zero,alpha--> c' = invMod2Pow(tau(alpha),3^{L+1}) * (3c+1)  mod 3^{L+1},
     KEPT iff c'%9 == alpha.
  Also one-edges at level L+1 act within the level by c'' = 2^{-tau} c' (admissible).

  Question A: does { c' : c in U_L-lift, alpha in X, fires } ∪ (one-edge closure) == U_{L+1}?

  But careful: the rep c at level L, when we go to level L+1, the SAME vertex has rep c (it lives
  at level L); the zero-edge uses 3c+1 with c the level-L rep, computed mod 3^{L+1}. Two different
  level-L reps c1==c2 mod 3^L but the vertex rep is unique (<3^L). Lifting c to level L+1 isn't free:
  the zero-edge input is 3*c+1 where c is the EXACT level-L representative (in [0,3^L)). So as c ranges
  over U_L (all level-L reps), 3c+1 ranges over {3c+1 : c in [0,3^L), c unit} -- a specific set mod 3^{L+1}.

  So: NewReps_{L+1} (from zero-edges, before one-edge closure) =
        { invMod2Pow(tau(a),3^{L+1}) * (3c+1) % 3^{L+1} : c in U_L, a in X, c'%9==a }.
  Then close under one-edges (multiply by 2^{-tau}, admissible) to get the full reachable level-(L+1) set.

  We test: starting from U_L = ALL units mod 3^L (the inductive hyp), is the one-step image
  (zero-edges + one-edge closure) == ALL units mod 3^{L+1}? If YES for a few L, and the map is
  manifestly translation-equivariant in the high digit, it's R-uniform => holds at R=46.

This DIRECTLY decides trap reachability: if level-(L+1) reps = all units for all L >= some base,
then 4 (a unit) is a reachable representative at level L+1 for the vertex (j=L+1-R, c=4) => TRAP REACHABLE.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]

def one_step_image(L):
    """Given U_L = all units mod 3^L as level-L reps, compute reachable level-(L+1) reps."""
    M=3**L; Mp=3**(L+1); inv2p=(Mp+1)//2
    UL=[c for c in range(M) if c%3!=0]
    reps=set()
    # zero-edges
    for c in UL:
        base=(3*c+1)%Mp
        for a in X:
            cp=(pow(inv2p,tau_a(a),Mp)*base)%Mp
            if cp%9==a:
                reps.add(cp)
    # close under one-edges at level L+1
    frontier=list(reps)
    while frontier:
        nf=[]
        for c in frontier:
            for a in X:
                cp=(pow(inv2p,tau_a(a),Mp)*c)%Mp
                if cp%9==a and cp not in reps:
                    reps.add(cp); nf.append(cp)
        frontier=nf
    return reps, Mp

print("=== one-step lift: U_L (all units mod 3^L) -> reachable level-(L+1) reps ===")
for L in range(2,11):
    reps,Mp=one_step_image(L)
    units_next=2*3**L
    print(f"L={L:2d} -> L+1={L+1:2d}: reachable reps = {len(reps)}/{units_next} units  ALL units? {len(reps)==units_next}")

print("""
If 'ALL units? True' for every L: the induction 'reps at level L = all units' is self-sustaining.
Base case: at the FIRST level where any vertex exists beyond start. The start (level R) is a single
unit (aS202 mod 3^R). One zero-edge gives several level-(R+1) reps; the question is whether they
generate ALL units mod 3^(R+1). For R=2,3 the exact BFS already showed YES (reps_at_top=all units
from Lstar=R+1 on). The one-step lift above shows the inductive STEP is unconditional once you have
all units at level L. The remaining gap: getting from the SINGLE start unit to all units at level R+1.
""")
