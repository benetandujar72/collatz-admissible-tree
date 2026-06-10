"""
B1 -- DIRECT exact check at the REAL scale R=46 (M=2, the m=1 barrier).
Is the trap vertex (j=1, c=4) reachable from InvStart(2) by a SINGLE zero-edge?
And does the dlog=2 / c==4 vertex appear, and is it m-precise-free on the way?

We also exhibit the explicit short path start -> trap, and check the CONSTRAINT
(no coarse-m-precise vertex before the trap).

Reminder of edge semantics (InverseGraph, exact):
 zero-edge v=(j,c) -> v'=(j+1,c'): need InX(c'), 3c+1 == 2^tau(c') c' (mod 3^(R+j+1)),
   c' is computed as invMod2Pow(tau,M') * (3c+1) % M', kept iff c'%9==alpha.
 So from start, c0 = aS202 % 3^46. Take the zero-edge whose alpha makes the target == 4?
 Target rep == 4 means alpha = 4%9 = 4, tau(4)=2. Check: is c' == invMod2Pow(2,M')*(3 c0+1) % M' == 4?
 That requires 3c0+1 == 2^2 * 4 = 16 (mod 3^47)? No: 3c0+1 == 2^tau(c') c' = 2^2 * 4 = 16 (mod 3^47).
 i.e. need 3*c0+1 == 16 mod 3^47. c0 = aS202 mod 3^46. 3*c0 = 3*aS202 mod 3^47 (since 3*(x mod 3^46) ==
 3x mod 3^47). 3*aS202 = 3 + 3^23. +1 = 4 + 3^23. Is 4+3^23 == 16 mod 3^47? 16-4=12=3+9? no.
 So the DIRECT single zero-edge to c'==4 does NOT fire from start (target 4 needs 3c0+1==16). Let's just
 compute the actual single-zero-edge targets from start and see what alphas fire and where they land,
 then do a SHORT bounded exact BFS at R=46 to FIND a path to c==4 (exact rep) with small j.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
aS202=1+3**22
from collections import deque

R=46
c0=aS202 % 3**R
print(f"R={R}, start c0 = aS202 mod 3^46 = {c0}")
print(f"  c0 % 9 = {c0%9} (==1, so NO one-edge out -- confirms S240)")

# single zero-edge targets from start
Mp=3**(R+1); inv2p=(Mp+1)//2
base=(3*c0+1)%Mp
print(f"\nSingle zero-edge targets from start (level {R+1}):")
for a in X:
    cp=(pow(inv2p,tau_a(a),Mp)*base)%Mp
    fires = (cp%9==a)
    print(f"  alpha={a} (tau={tau_a(a)}): target c'={cp}  c'%9={cp%9}  fires={fires}  is_trap(c'==4)={cp==4}")

# bounded exact BFS at R=46 to find ANY reachable vertex with c==4 (the exact trap), small j.
# Track (j,c) exactly; prune: keep BFS until trap found or frontier too big / level cap.
def find_trap(R, levelcap, statecap):
    start=(0, aS202 % 3**R)
    seen={start}; dq=deque([start])
    while dq and len(seen)<statecap:
        j,c=dq.popleft(); L=R+j
        if c==4:
            return (j,c), len(seen)
        M=3**L; inv2=(M+1)//2
        for a in X:
            cp=(pow(inv2,tau_a(a),M)*c)%M
            if cp%9==a and (j,cp) not in seen:
                seen.add((j,cp)); dq.append((j,cp))
        if L+1<=R+levelcap:
            Mp=3**(L+1); inv2p=(Mp+1)//2
            base=(3*c+1)%Mp
            for a in X:
                cp=(pow(inv2p,tau_a(a),Mp)*base)%Mp
                if cp%9==a and (j+1,cp) not in seen:
                    seen.add((j+1,cp)); dq.append((j+1,cp))
    return None, len(seen)

print("\n=== bounded exact BFS at R=46 for the trap c==4 ===")
res,nseen=find_trap(R, levelcap=6, statecap=3_000_000)
print(f"  trap found: {res}  (states explored {nseen})")
