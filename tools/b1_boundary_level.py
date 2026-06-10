"""
B1 -- THE decisive test: is the trap residue 4 reachable AT THE BOUNDARY LEVEL?

The trap T = vertex (j, c) with c == 4 mod 3^(R+j), c the representative (< 3^(R+j)), i.e. c==4 exactly.
A reachable vertex at level R+j has a representative c in [0,3^(R+j)). For it to BE the trap,
its representative must equal 4, i.e. c == 4 mod 3^(R+j) AT ITS OWN level.

In the truncated BFS we found: for every t, EVERY unit mod 3^t is reachable (as c mod 3^t at
SOME vertex). But the vertex realizing 'c == 4 mod 3^t' generally sits at a level L = R+j with
L possibly > t, so its representative is 4 + 3^t*(...) != 4 -- NOT the trap.

The trap needs the representative == 4 at level EXACTLY R+j, i.e. we need a reachable vertex whose
level L satisfies c == 4 mod 3^L with c<3^L, i.e. c==4. Equivalently: reachable (j,c) with c==4 and
the modulus is 3^(R+j) -- so we need '4 mod 3^(R+j)' realized by a vertex AT level R+j whose
representative is 4. Since 4 < 3^(R+j), '4 mod 3^(R+j)' as a representative is just 4.

So: TRAP reachable  <=>  exists reachable vertex (j, c) with c == 4 (the integer 4).
The representative c is c_full mod 3^(R+j). c==4 means c_full == 4 mod 3^(R+j).

Now, KEY: a vertex's representative c is computed by the edge maps mod 3^(R+j). After j zero-edges
the level is R+j. The representative c==4 means the FULL R+j digits are (1,1,0,0,...,0).

I'll test reachability of the EXACT integer 4 by tracking, in the mod-3^t BFS, the MINIMUM level
at which each residue is first reached, AND whether residue '4 mod 3^t' is ever reached by a vertex
whose level is EXACTLY its representative's modulus (i.e. a vertex at level t with rep < 3^t equal to
4 mod 3^t). Concretely: do exact BFS tracking (level L=R+j, c mod 3^t) but bounding L<=t (so the rep
mod 3^t IS the full rep when L<=t). When L==t the rep mod 3^t is the true representative.

We do: for target level L*, run exact BFS with modulus 3^(L*) but ONLY tracking reps, bounding j so
R+j<=L*. Check if (j=L*-R, c==4) reachable. Use SMALL R to make 3^(L*) enumerable.
Because the question 'is exact 4 reachable' should be structurally R-robust, small R reveals it.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
aS202=1+3**22
from collections import deque

def exact_reach(R, Lstar):
    """exact BFS, modulus grows with level; track representative c at level R+j, j from 0..Lstar-R.
       Return set of (j,c) reachable, and whether any c==4."""
    seen=set();
    start=(0, aS202 % 3**R)
    seen.add(start); dq=deque([start])
    trap=set()
    while dq:
        j,c=dq.popleft()
        L=R+j
        if c==4: trap.add((j,c))
        M=3**L; inv2=(M+1)//2
        # one-edges (same level)
        for a in X:
            cp=(pow(inv2,tau_a(a),M)*c)%M
            if cp%9==a and (j,cp) not in seen:
                seen.add((j,cp)); dq.append((j,cp))
        # zero-edges -> level L+1, only if L+1<=Lstar
        if L+1<=Lstar:
            Mp=3**(L+1); inv2p=(Mp+1)//2
            base=(3*c+1)%Mp
            for a in X:
                cp=(pow(inv2p,tau_a(a),Mp)*base)%Mp
                if cp%9==a and (j+1,cp) not in seen:
                    seen.add((j+1,cp)); dq.append((j+1,cp))
    return seen, trap

# small R, push Lstar as far as memory allows
for R in [2,3]:
    for Lstar in range(R, R+14):
        seen,trap=exact_reach(R,Lstar)
        # count reps at top level
        toplevel=Lstar
        top=[(j,c) for (j,c) in seen if R+j==toplevel]
        units_at_top=2*3**(toplevel-1)
        print(f"R={R} Lstar={Lstar}: |reach|={len(seen)}  reps_at_top_level={len(top)}/{units_at_top}  TRAP(c==4 ever)={len(trap)>0} {sorted(trap)[:4]}")
        if len(seen)>3_000_000:
            print("   (stopping R, state space large)"); break
