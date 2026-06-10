"""
B1 -- PROVE: Reach_t = all units mod 3^t (residues coprime to 3).
Therefore NO mod-3^t congruence invariant separates trap(4, a unit) from start.

We verify Reach_t == {c in Z/3^t : c%3 != 0} for t=1..11, and identify the minimal
generating moves. Then we explain WHY structurally (so it can become a Lean lemma).
"""
def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
aS202=1+3**22

def reach_mod(t, allow_zero=True, allow_one=True):
    M=3**t; inv2=(M+1)//2
    invpow={a: pow(inv2, tau(a), M) for a in X}
    start=aS202 % M
    seen={start}; frontier=[start]
    while frontier:
        nf=[]
        for c in frontier:
            if allow_one:
                for a in X:
                    cp=(invpow[a]*c)%M
                    if cp%9==a and cp not in seen: seen.add(cp); nf.append(cp)
            if allow_zero:
                base=(3*c+1)%M
                for a in X:
                    cp=(invpow[a]*base)%M
                    if cp%9==a and cp not in seen: seen.add(cp); nf.append(cp)
        frontier=nf
    return seen

for t in range(1,12):
    M=3**t
    units={c for c in range(M) if c%3!=0}
    R=reach_mod(t)
    print(f"t={t:2d}: Reach==units? {R==units}  |Reach|={len(R)} |units|={len(units)}")

print("\n--- which moves are needed? one-only vs zero-only ---")
for t in [4,6,8]:
    M=3**t; units={c for c in range(M) if c%3!=0}
    Ron=reach_mod(t, allow_zero=False, allow_one=True)
    Rzero=reach_mod(t, allow_zero=True, allow_one=False)
    print(f"t={t}: one-edges-only reach={len(Ron)} (units={len(units)}); zero-edges-only reach={len(Rzero)}")

# Structural why: a one-edge sends c -> c' with c == 2^tau c' i.e. c' == 2^{-tau} c.
# As alpha ranges over X with the admissibility c'%9==alpha, and tau(alpha) covers a set of
# exponents, the one-edge orbit multiplies c by various 2^{-tau}. Combined with zero-edge's
# affine 3c+1 (which is c->(3c+1), a unit since !=0 mod3) and rescale, the semigroup acts
# transitively on units. Let's confirm the one-edge alone is multiplication by powers of 2:
print("\n--- one-edge as multiplication by 2^{-tau}, reachable 2-power coset of start ---")
for t in [4,6]:
    M=3**t; inv2=(M+1)//2
    start=aS202%M
    # one-edge keeps c in start * <2>?  the multiplier is 2^{-tau}, a power of 2. So one-edges keep
    # c in the coset start*<2> = <2> (since start is a unit) -- actually the whole cyclic group <2> = all units
    # because 2 is a primitive root! So one-edges ALONE, if all tau-steps were always admissible,
    # would reach all units. Check the actual one-edge-only reach vs <2>-orbit of start:
    g=set(); v=start
    for _ in range(2*3**(t-1)+1):
        g.add(v); v=(v*2)%M
    Ron=reach_mod(t, allow_zero=False, allow_one=True)
    print(f"t={t}: <2>-orbit size={len(g)} (=all units); one-edge-only reach={len(Ron)}; Ron subset of <2>? {Ron<=g}")
