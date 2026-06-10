"""
B1 -- THE CONSTRAINED reachability: can we reach the trap (c==4 at level R+j) WITHOUT
first passing through a coarse-m-precise vertex (c == 1 mod 3^(R-22+j))?

The (m+1)-barrier: R = Rbar = 22(m+1)+2 = 22m+24. m-precise (coarse) level = 22m+2+j = R-22+j.
A vertex (j,c) is m-precise iff c == 1 mod 3^(R-22+j).

We do exact BFS at SMALL R (so reps enumerable), but R must be >= 24 for the coarse level
R-22+j>=2 to be meaningful... Actually for the structural question use the SHIFTED model:
the coarse-precise level is (R-22)+j; the trap level is R+j. Their GAP is exactly 22 (the window).
So rescale: let r := R-22 = 22m+2 (the coarse base). Then:
   coarse-m-precise: c == 1 mod 3^(r+j)
   trap:            c == 4 mod 3^(r+22+j)
   start:           c0 = aS202 mod 3^(r+22),  with aS202 = 1+3^22.
For m=1: r=24. The gap-22 between 'precise modulus' and 'trap modulus' is the structural heart.

To make it enumerable, shrink BOTH the base r and keep the gap g (instead of 22) as a parameter,
and check the constrained reachability as a function of (r, g). The real case is large r, g=22.
We test small r and g=2,3,4 to see the PATTERN: is the trap reachable while staying non-precise?

Model: vertex (j, c) with c a rep mod 3^(r+g+j).
  precise(j,c)  := c % 3^(r+j) == 1
  trap(j,c)     := c == 4   (rep mod 3^(r+g+j), and 4<modulus so ==4 exactly)
  start         := (0, aS202_small mod 3^(r+g)) where aS202_small = 1 + 3^g (the analogue).
Edges: exact one/zero as usual at level r+g+j.
CONSTRAINED BFS: never expand a precise vertex (we want trap strictly before any precise vertex).
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
from collections import deque

def constrained_trap(r, g, levelcap, statecap=4_000_000, allow_expand_precise=False):
    """start = 1+3^g mod 3^(r+g). trap=c==4 at level r+g+j. precise: c==1 mod 3^(r+j).
       Returns (trap_reachable_unconstrained, trap_reachable_constrained, first_path_info)."""
    aS = 1 + 3**g
    base_level = r+g
    start=(0, aS % 3**base_level)
    # is start precise? c0 % 3^r == 1? aS=1+3^g, mod 3^r: if g<r -> 1+3^g != 1 (since g>=1) -> NOT precise (good, like real start)
    def precise(j,c): return c % 3**(r+j) == 1
    def trap(j,c): return c==4
    # UNCONSTRAINED BFS
    def bfs(constrain):
        seen={start}; dq=deque([start]); found=None
        while dq and len(seen)<statecap:
            j,c=dq.popleft(); L=base_level+j
            if trap(j,c):
                found=(j,c); break
            if constrain and precise(j,c):
                continue  # do not expand precise vertices
            M=3**L; inv2=(M+1)//2
            for a in X:
                cp=(pow(inv2,tau_a(a),M)*c)%M
                if cp%9==a and (j,cp) not in seen:
                    seen.add((j,cp)); dq.append((j,cp))
            if j+1<=levelcap:
                Mp=3**(L+1); inv2p=(Mp+1)//2
                bb=(3*c+1)%Mp
                for a in X:
                    cp=(pow(inv2p,tau_a(a),Mp)*bb)%Mp
                    if cp%9==a and (j+1,cp) not in seen:
                        seen.add((j+1,cp)); dq.append((j+1,cp))
        return found, len(seen)
    unc,nu=bfs(False)
    con,nc=bfs(True)
    return unc, con, nu, nc, precise(*start)

print("=== Constrained trap reachability: trap BEFORE any coarse-precise vertex ===")
print("    (small base r, gap g; real case r=24,g=22)")
print(f"{'r':>3} {'g':>3} {'start_precise':>13} {'trap_unconstr':>14} {'trap_CONSTRAINED':>17}")
for r in [2,3,4]:
    for g in [2,3,4]:
        unc,con,nu,nc,sp = constrained_trap(r,g, levelcap=g+4)
        print(f"{r:>3} {g:>3} {str(sp):>13} {str(unc is not None):>14} {str(con is not None):>17}   (unc@{unc}, con@{con})")
