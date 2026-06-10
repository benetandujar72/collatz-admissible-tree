"""
Angle B1 -- High-modulus invariant search for the Wall-B trap-reachability question.

Faithful model of the InverseGraph (S215) edges + DlogReachable cocycle.
Goal: find an invariant I preserved by BOTH edge types with I(InvStart) != I(trap),
or prove no low-modulus one exists and locate the minimal separating modulus.

VERIFIED FACTS (from Lean sources, do NOT re-derive):
  tau: n%9 -> {1:2, 2:1, 4:2, 5:3, 7:4, 8:1, else 0}
  InX: n%9 in {1,2,4,5,7,8}
  aS202 = 1 + 3^22 = 31381059610,  aS202 % 9 = 1
  InvStart(m) = (j=0, c = aS202 % 3^(22m+2))
  R = 22m+2.
  one-edge v->v' (same j): v.c == 2^tau(v'.c) * v'.c  (mod 3^(R+j))
  zero-edge v->v' (j->j+1): 3*v.c+1 == 2^tau(v'.c) * v'.c (mod 3^(R+j+1)), weight tau-2
  GOAL: v.c == 1 (mod 3^(R+j))
  TRAP T: v.c == 4 (mod 3^(R+j))   (dlog=2; the deep-one-edge source)
"""

def tau(n):
    r = n % 9
    return {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}.get(r, 0)

def InX(n):
    return (n % 9) in (1, 2, 4, 5, 7, 8)

X = [1, 2, 4, 5, 7, 8]

aS202 = 1 + 3**22
assert aS202 == 31381059610
assert aS202 % 9 == 1

# ---- discrete log base 2 mod 3^k. 2 is a primitive root mod 3^k; order = 2*3^(k-1).
def order_two(k):
    return 2 * 3**(k - 1)

def dlog(k, c):
    """discrete log of c base 2 mod 3^k. c must be a unit (coprime to 3)."""
    M = 3**k
    c %= M
    assert c % 3 != 0, f"c={c} not a unit mod 3^{k}"
    ordr = order_two(k)
    # 2 is primitive root: brute over the order. For small k only.
    val = 1
    for t in range(ordr):
        if val == c:
            return t
        val = (val * 2) % M
    raise RuntimeError("dlog not found -- 2 not primitive?")

# sanity: 2 primitive root mod 3^k for small k, and dlog(4)=2, dlog(1)=0
for k in range(1, 8):
    M = 3**k
    seen = set()
    v = 1
    for t in range(order_two(k)):
        seen.add(v); v = (v*2) % M
    units = [u for u in range(M) if u % 3 != 0]
    assert len(seen) == len(units), f"2 NOT primitive mod 3^{k}: {len(seen)} vs {len(units)}"
print("2 is a primitive root mod 3^k for k=1..7: CONFIRMED")
print("dlog(k=3, 4) =", dlog(3,4), " dlog(k=3,1) =", dlog(3,1))

# ---- d0 = dlog(aS202) at various levels.
print("\n=== d0 = dlog(aS202 mod 3^k) at the start (j=0), for m=1 (R=24) the level is k=24 ===")
print("aS202 = 1 + 3^22.  aS202 mod 3^k:")
for k in [1,2,3,4,5,6,7]:
    M = 3**k
    a = aS202 % M
    d = dlog(k, a)
    print(f"  k={k:2d}: aS202%3^k={a:8d}  dlog={d:5d}  (order={order_two(k)})  dlog%2={d%2}  a%3={a%3}")
