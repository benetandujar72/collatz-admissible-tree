"""
B1 -- the BASE CASE: from a SINGLE unit seed at level L (the start, with c%9 in various classes),
how fast does the reachable set fill all units? Test R-uniformity of the spread.

The start has c0%9 == 1 (aS202). From a c%9==1 vertex there is NO one-edge (S240). So the ONLY
move is a zero-edge. After ONE zero-edge we have a few level-(L+1) reps in classes {1,2,5,7}
(the alphas that fired from start). From those, one-edges + zero-edges spread.

We test: seed = single unit u at level L; BFS within level window [L, L+W]; does it reach all
units mod 3^L (the within-level fill), and all units mod 3^(L+w)? Crucially test whether the
SPREAD is independent of WHICH unit u we start from (translation/structure uniformity), and
whether c%9==1 seeds (like the real start) still fill.

If from ANY single unit seed the reachable set fills all units at level L+W for modest W,
uniformly in L, then the base case at R=46 holds (the start is one such seed) and the trap
(c==4 at level R+j) is REACHABLE. This is the rigorous closer modulo formalizing the uniform
spread lemma.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
def tau(n): return {1:2,2:1,4:2,5:3,7:4,8:1}.get(n%9,0)
X=[1,2,4,5,7,8]
from collections import deque

def spread_from_seed(L, seed, W):
    """BFS from (level L, rep seed) within levels [L, L+W]. Return reps grouped by level."""
    start=(L, seed % 3**L)
    seen={start}; dq=deque([start])
    while dq:
        lvl,c=dq.popleft()
        M=3**lvl; inv2=(M+1)//2
        for a in X:
            cp=(pow(inv2,tau_a(a),M)*c)%M
            if cp%9==a and (lvl,cp) not in seen:
                seen.add((lvl,cp)); dq.append((lvl,cp))
        if lvl+1<=L+W:
            Mp=3**(lvl+1); inv2p=(Mp+1)//2
            base=(3*c+1)%Mp
            for a in X:
                cp=(pow(inv2p,tau_a(a),Mp)*base)%Mp
                if cp%9==a and (lvl+1,cp) not in seen:
                    seen.add((lvl+1,cp)); dq.append((lvl+1,cp))
    byL={}
    for (lvl,c) in seen: byL.setdefault(lvl,set()).add(c)
    return byL

print("=== spread from a SINGLE unit seed, various seeds and levels ===")
aS202=1+3**22
# test seeds: the real start residue's low part, and a few representatives of each mod-9 class
for L in [4,5,6]:
    for seed_label, seed in [("aS202", aS202%3**L), ("u%9=1: 1", 1), ("u%9=2: 2", 2),
                             ("u%9=4: 4", 4), ("u%9=7: 7", 7), ("u%9=8: 8", 8)]:
        byL=spread_from_seed(L, seed, W=3)
        line=[]
        for lvl in sorted(byL):
            units=2*3**(lvl-1)
            line.append(f"L{lvl}:{len(byL[lvl])}/{units}{'=ALL' if len(byL[lvl])==units else ''}")
        print(f"  base L={L} seed={seed_label:12s}: " + "  ".join(line))
    print()
