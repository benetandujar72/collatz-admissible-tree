"""
Fast discrete log base 2 modulo 3^k.  Group is cyclic of order n = 2*3^(k-1),
with 2 a generator (verified: 2 is a primitive root mod 3^k for all k>=1).

Pohlig-Hellman over n = 2 * 3^(k-1):
  - component mod 2:  from c mod 3  (sign / Teichmuller bit), since 2 == -1 mod 3.
  - component mod 3^(k-1): Hensel-lift / iterative digit extraction in the 3-Sylow.

We extract the dlog by computing x = dlog(c) with:
  x ≡ s (mod 2),   x ≡ y (mod 3^(k-1)),  then CRT.
For the 3-part we use the standard p-adic log:  let g3 = 2^2 (generator of the
3-Sylow of order 3^(k-1), since 2^2 has order 3^(k-1)).  We need y3 with
g3^{y3} == c * 2^{-s}  in the 3-Sylow.  Solve digit by digit (base 3).
This is O(k^2) multiplications -- fast for k up to a few hundred.
"""

def _dlog3_sylow(target, M, k):
    """Solve 2^(2*y) == target (mod M=3^k), where target is in the 3-Sylow
    (an element of order dividing 3^(k-1)).  Return y in [0, 3^(k-1))."""
    # generator of 3-Sylow:
    g = pow(2, 2, M)              # order 3^(k-1)
    # digit extraction: y = sum_{i=0}^{k-2} d_i 3^i
    y = 0
    n3 = 3**(k-1)
    # We use: to find y mod 3^(i+1) given y mod 3^i, raise to the cofactor.
    # Standard PH for prime-power order p^e with p=3, e=k-1.
    e = k-1
    gamma = pow(g, 3**(e-1), M) if e >= 1 else 1   # element of order 3
    # precompute discrete log table for the order-3 subgroup {1, gamma, gamma^2}
    table = {}
    acc = 1
    for d in range(3):
        table[acc] = d
        acc = (acc * gamma) % M
    x = 0
    ginv = pow(g, -1, M)
    for i in range(e):
        # h = (g^{-x} * target)^{3^{e-1-i}}
        h = (pow(ginv, x, M) * target) % M
        h = pow(h, 3**(e-1-i), M)
        d_i = table[h]
        x += d_i * (3**i)
    return x % n3

def fast_dlog(c, k):
    """dlog base 2 of c mod 3^k.  Returns t in [0, 2*3^(k-1)) with 2^t==c, or
    None if c not a unit."""
    M = 3**k
    c %= M
    if c % 3 == 0:
        return None
    if k == 1:
        return 0 if c % 3 == 1 else 1
    n = 2 * 3**(k-1)
    # sign bit s: 2^t == c mod 3 => (-1)^t == c mod 3 => t even iff c==1 mod3
    s = 0 if c % 3 == 1 else 1
    # remove sign: target = c * 2^{-s}, now in 3-Sylow (== 1 mod 3)
    tgt = (c * pow(pow(2, s, M), -1, M)) % M
    assert tgt % 3 == 1, (c,k,s,tgt%3)
    y = _dlog3_sylow(tgt, M, k)   # 2^(2y) == tgt
    # t == s (mod 2),  t == 2y (mod 3^(k-1)) ... wait: 2^t = 2^s * 2^(2y) => t = s+2y
    t = (s + 2*y) % n
    return t

if __name__ == "__main__":
    # self-test against sympy
    from sympy.ntheory.residue_ntheory import discrete_log as _dl
    import random
    for k in range(1, 12):
        M = 3**k
        for _ in range(30):
            c = random.randrange(1, M)
            if c % 3 == 0: continue
            f = fast_dlog(c, k)
            assert pow(2, f, M) == c % M, (k, c, f)
            s = _dl(M, c % M, 2)
            assert f == s, (k, c, f, s)
    print("fast_dlog OK against sympy for k=1..11")
    # timing on big k
    import time
    for k in [24, 46, 68]:
        M=3**k; c = (1 + 3**22) % M
        t0=time.time(); f=fast_dlog(c,k); dt=time.time()-t0
        assert pow(2,f,M)==c%M
        print(f" k={k}: dlog(aS202)={f}  ({dt*1000:.2f} ms)")
