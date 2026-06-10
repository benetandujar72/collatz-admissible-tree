"""
B1 -- The j<->modulus COUPLING. The trap is c == 4 mod 3^(R+j), level GROWS with j.

A vertex (j,c) is canonical with c < 3^(R+j) (the residue representative). The trap asks
c == 4 mod 3^(R+j) i.e. c == 4 EXACTLY as a representative iff c<3^(R+j): so c==4 literally,
OR c == 4 + multiple... no: c is the representative in [0,3^(R+j)), and trap means the residue is 4,
so the canonical representative c == 4. Wait, 4 < 3^(R+j) always (R>=46), so trap <=> c==4 exactly.

Hold on. Let me re-examine. The trap cylinder T = { v : v.c == 4 (mod 3^(R+v.j)) }. The graph
vertices carry c as the representative mod 3^(R+j) (outgoingEdges does y%M). So v.c in [0, 3^(R+j)).
Then v.c == 4 mod 3^(R+j) with v.c < 3^(R+j) means v.c == 4 exactly. So the trap is the SINGLE
vertex (j, 4) for each j!  i.e. c is LITERALLY 4.

So reaching the trap = reaching a vertex whose representative c == 4 at SOME level j.
The truncated analysis (Reach_t = units) said: 4 mod 3^t is reachable for each t. But that means
there's a reachable vertex with c == 4 mod 3^t -- NOT necessarily c == 4 exactly (c could be
4 + 3^t * (anything) at a higher level). The EXACT trap c==4 needs c==4 mod 3^(R+j), the FULL level.

This is the crux: low-t reachability of '4 mod 3^t' does NOT imply reachability of the exact rep 4.
The exact rep 4 at level R+j requires ALL R+j ternary digits to be those of 4 = (...,0,0,1,1) i.e.
4 = 1 + 3, so digits: d0=1,d1=1,d2=0,...,d_{R+j-1}=0. That's c==4 with rho+(c-1)=nu3(3)=1 and the
top R+j-2 digits all ZERO. i.e. c == 4 mod 3^(R+j) <=> c-4 == 0 mod 3^(R+j) <=> (since c<3^(R+j)) c==4.

So: TRAP = reachable vertex with representative c EXACTLY 4 at its level R+j.
Equivalent dlog statement: dlog_{R+j}(c) == 2 (since 2^2=4 and dlog is injective). dlog==2 EXACT,
not just ==2 mod something. dlog(c)==2 means c == 4 mod 3^(R+j) (full).

Now dlog(c) is a number in [0, 2*3^{R+j-1}). dlog==2 is ONE specific tiny value.
The start has dlog == 0 mod 2*3^21 (huge), and the question is whether dlog can be driven to
EXACTLY 2 at the working level.

KEY: dlog == 2 (exact) <=> dlog == 2 mod 2*3^{R+j-1}, the FULL order. We cannot truncate.
But we CAN ask: is dlog == 2 mod 2*3^{s} reachable, for growing s, AT A VERTEX WHOSE LEVEL >= s+1?
That couples s to j. Let's study the reachable set of dlog at level-(R+j) reduced mod 2*3^s,
as a function of how many zero-edges (=j) we've taken. Because each zero-edge raises the level by 1.
"""
def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
aS202=1+3**22
import sys; sys.path.insert(0,".")
from b1_dlog_fast import dlog_fast

# Reachable EXACT representatives c at small levels: do exact BFS tracking the FULL representative
# c mod 3^(R+j) -- but that's huge. Instead use a SMALL R to make it tractable and see the pattern,
# then argue the general R is analogous. Use R=2 (smallest with 9|3^R) -> level 2+j. trap c==4.
# Actually the structure of reachability of EXACT 4 should not depend on R in an essential way;
# test with small R to ENUMERATE exact representatives.

def bfs_exact(R, Q, maxlevel):
    """exact BFS tracking representative c at level R+j. trap = c==4. Return reachable (j,c)."""
    from collections import deque
    start=(0, aS202 % 3**R)
    seen={start}; dq=deque([start])
    trap=[]
    while dq:
        j,c=dq.popleft()
        if c==4: trap.append((j,c))
        # one-edges
        M=3**(R+j); inv2=(M+1)//2
        for a in X:
            cp=(pow(inv2,tau(a),M)*c)%M
            if cp%9==a and (j,cp) not in seen:
                seen.add((j,cp)); dq.append((j,cp))
        if j<Q and j<maxlevel:
            Mp=3**(R+j+1); inv2p=(Mp+1)//2
            base=(3*c+1)%Mp
            for a in X:
                cp=(pow(inv2p,tau(a),Mp)*base)%Mp
                if cp%9==a and (j+1,cp) not in seen:
                    seen.add((j+1,cp)); dq.append((j+1,cp))
    return seen, trap

# enumerate with small R to see if exact 4 is reachable
for R in [2,3,4]:
    for Q in [R+4, R+8]:
        seen,trap=bfs_exact(R,Q,maxlevel=Q)
        by_level={}
        for (j,c) in seen: by_level[j]=by_level.get(j,0)+1
        print(f"R={R} Q={Q}: |reach|={len(seen)} by_level={dict(sorted(by_level.items()))} TRAP(c==4) reached: {len(trap)>0} {trap[:3]}")
