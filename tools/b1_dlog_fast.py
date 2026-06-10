"""
Fast discrete log base 2 mod 3^k via the structure (ZMod 3^k)^x = <-1> x <1+3>.
  2 = -1 * (1+3)?  Check: -1 mod 3^k = 3^k - 1. (1+3) = 4. (-1)*4 = -4 = 3^k-4.
  Actually 2 = (-1)*(-2). Better: use that 2 generates the whole group (primitive root).

We compute dlog by: order N = 2*3^(k-1).
  sign bit s = dlog % 2  is  [c % 3 == 2]  (since 2 == -1 mod 3).  [VERIFIED in Lean: dlog_mod_two]
  Then dlog = s + 2*t where 2^dlog = c, i.e. (2^2)^t = c * 2^{-s} = c * (inv2)^s.
    Let g = 4 = 2^2, which has order 3^(k-1) (generates the principal units 1+3Z mod 3^k... check).
    We need dlog_g( c * inv2^s ) over Z/3^(k-1), where the target is a principal unit (==1 mod 3).
  3-adic log: for u == 1 mod 3, write u = 1 + 3w; log via Pohlig-Hellman base-3 digit lifting is robust.

We use a clean Pohlig-Hellman over the 3-power part: solve g^t == h (mod 3^k) with g=4 (order 3^(k-1)),
h a principal unit, by lifting one 3-adic digit at a time.  O(k) multiplications.
"""

def two_pow_mod(e, M):
    return pow(2, e, M)

def dlog_fast(k, c):
    """dlog base 2 of unit c mod 3^k. Returns t in [0, 2*3^(k-1))."""
    M = 3**k
    c %= M
    assert c % 3 != 0
    if k == 1:
        # group {1,2}, 2^0=1,2^1=2
        return 0 if c == 1 else 1
    N = 2 * 3**(k-1)
    # sign bit
    s = 1 if (c % 3 == 2) else 0
    inv2 = (M + 1)//2  # 2^{-1} mod M
    h = (c * pow(inv2, s, M)) % M   # now h == 1 mod 3 (principal unit)
    assert h % 3 == 1, (k, c, h % 3)
    # solve 4^t == h mod 3^k, t in [0, 3^(k-1)), via Hensel/Pohlig-Hellman base 3.
    # g = 4 has order 3^(k-1). Lift digit by digit.
    g = 4
    t = 0
    order = 3**(k-1)
    # digit lifting: find t = sum d_i 3^i, i=0..k-2
    # standard PH for prime-power group of order 3^(k-1):
    # for i in 0..k-2: compute (g^{-t} * h)^{3^(k-2-i)} == (g^{3^(k-2)})^{d_i}
    gpows = {}
    base = pow(g, 3**(k-2), M)  # element of order 3
    # precompute base^0,1,2
    bt = 1
    for d in range(3):
        gpows[bt] = d
        bt = (bt * base) % M
    ginv = pow(g, -1, M)
    for i in range(k-1):
        # current residual
        e = (pow(ginv, t, M) * h) % M
        ex = pow(e, 3**(k-2-i), M)
        di = gpows[ex]
        t += di * 3**i
    # verify
    assert pow(g, t, M) == h, (k, c, t, h)
    res = (s + 2*t) % N
    assert pow(2, res, M) == c, (k, c, res)
    return res

if __name__ == "__main__":
    # cross-check vs brute force for k=1..7
    def dlog_brute(k, c):
        M = 3**k; c %= M
        v = 1
        for tt in range(2*3**(k-1)):
            if v == c: return tt
            v = (v*2) % M
        raise RuntimeError
    import itertools
    for k in range(1, 8):
        M = 3**k
        for c in range(M):
            if c % 3 == 0: continue
            a = dlog_brute(k, c); b = dlog_fast(k, c)
            assert a == b, (k, c, a, b)
    print("dlog_fast matches brute force for k=1..7, all units: CONFIRMED")
    # now the real d0 at k=24..56
    aS202 = 1 + 3**22
    print("\nd0 = dlog(aS202 mod 3^k) for k = 23..56 (start level for m=1 is k=24=22*1+2):")
    for k in [22,23,24,25,30,40,46,56]:
        a = aS202 % 3**k
        d = dlog_fast(k, a)
        print(f"  k={k:2d}: dlog={d}  (order 2*3^{k-1} = {2*3**(k-1)})  d%2={d%2}  d%6={d%6}  d%18={d%18}")
