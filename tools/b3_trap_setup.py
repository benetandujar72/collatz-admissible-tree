"""
Angle B3 setup: precise arithmetic of the inverse cylinder graph, the trap T,
and the 'deep one-edge straight to goal' device.

Verified-fact recap (from the Lean sources, taken as GIVEN):
 - tau table on c%9 over X={1,2,4,5,7,8}: 1->2, 2->1, 4->2, 5->3, 7->4, 8->1.
 - aS202 = 1 + 3^22.  R = 22m+2.
 - One-edge v->v' (same j): v.c == 2^tau(v'.c) * v'.c (mod 3^(R+j)); v'.c%9 in X.
 - Zero-edge v->v' (j->j+1): 3*v.c+1 == 2^tau(v'.c) * v'.c (mod 3^(R+j+1)); v'.c%9 in X.
 - GOAL at vertex v: v.c == 1 (mod 3^(R+v.j)).
 - dlog = discrete log base 2 mod 3^k (2 is a primitive root mod 3^k for k>=1).
 - InvStart(m) = (j=0, c = aS202 mod 3^(22m+2)) = (0, 1+3^22) for m>=1.

The trap cylinder (as stated):  T := { v : v.c == 4 (mod 3^(R+v.j)) }, i.e. dlog(v.c)=2
at the vertex's OWN full precision 3^(R+v.j).
"""

TAU = {1:2, 2:1, 4:2, 5:3, 7:4, 8:1}
X = set(TAU.keys())

def tau(c):
    return TAU.get(c % 9, 0)

def order2(k):
    # order of 2 mod 3^k = 2*3^(k-1)
    return 2 * 3**(k-1)

def dlog(c, k):
    """Discrete log base 2 of c mod 3^k.  Fast: solve 2^t == c (mod 3^k) by
    lifting the order-(2*3^(k-1)) cyclic group.  Use the structure
    t mod 2 (sign, from c mod 3) and t mod 3^(k-1) (3-adic part) via Hensel.
    Implemented with sympy's discrete_log for robustness."""
    from sympy.ntheory.residue_ntheory import discrete_log as _dl
    M = 3**k
    c %= M
    if c % 3 == 0:
        return None
    # order of the group is n = 2*3^(k-1); 2 is a generator.
    return _dl(M, c, 2)

def aS202():
    return 1 + 3**22

# --- The 'deep one-edge straight to goal' device --------------------------
# We have a SOURCE vertex u = (j, c_u). A one-edge u -> v' keeps j fixed and
# requires  c_u == 2^tau(v'.c) * v'.c  (mod 3^(R+j)).  For v' to be a GOAL we
# need v'.c == 1 (mod 3^(R+j)).  Substituting the goal residue v'.c == 1:
#   the one-edge consistency at the goal forces  c_u == 2^tau(1) * 1 == 2^2 == 4
#   (mod 3^(R+j)),  since tau is read off v'.c%9 = 1%9 = 1 -> tau=2.
# THIS is exactly the trap:  a source that can one-edge straight to a goal must
# have c_u == 4 (mod 3^(R+j)), i.e. dlog(c_u) = 2 at full precision.
#
# Conversely if c_u == 4 (mod 3^(R+j)) then v' defined by v'.c == 4 * inv(2^2)
# == 4 * inv(4) == 1 (mod 3^(R+j)) is a goal, and v'.c%9 = 1 in X, tau=2
# matches.  So:
#   T (source can deep-one-edge straight to goal)  <==>  c_u == 4 (mod 3^(R+j)).
# Confirmed: the device target is the goal itself, and the trap is c==4 full-prec.

def verify_device(m=1, j=0):
    R = 22*m + 2
    k = R + j
    M = 3**k
    # If source c_u == 4 mod M, the unique one-edge target with tau-consistency
    # landing the goal:
    inv4 = pow(4, -1, M)
    vprime_c = (4 * inv4) % M   # == 1
    assert vprime_c % 9 == 1 and vprime_c == 1, vprime_c
    assert tau(1) == 2
    # consistency: c_u == 2^tau(1) * v'.c == 4 * 1 == 4
    assert (2**tau(1) * vprime_c) % M == 4 % M
    print(f"[device] m={m} j={j} k={k}: trap source c==4 -> goal v'.c==1 OK; dlog(4,k)={dlog(4,k)}")

if __name__ == "__main__":
    print("tau table:", TAU)
    print("aS202 = 1 + 3^22 =", aS202(), " aS202%9 =", aS202()%9, " dlog(aS202 mod 9-lift?)")
    for k in range(1,7):
        print(f"  k={k}: order2={order2(k)}  dlog(4,{k})={dlog(4,k)}  dlog(1,{k})={dlog(1,k)}")
    # d0 = dlog(aS202) at the start modulus 3^(22m+2) for m=1 (k=24)
    for m in [1,2]:
        k = 22*m+2
        d0 = dlog(aS202() % 3**k, k)
        print(f"  m={m}: start k={k}  d0 = dlog(aS202) = {d0}   (mod order {order2(k)})")
    verify_device(1,0)
    verify_device(1,3)
