"""
B1 -- The j <-> dlog COUPLING (the last possible obstruction).

The trap needs dlog == 2 at the FULL level R+j. To be at level R+j you took j zero-edges.
Question: is there a constraint linking the reachable dlog-residue to j?

We track the JOINT reachable set { (j, D mod 2*3^s) } for fixed small s, over the faithful
dlog dynamics (one-edges keep j, zero-edges j+1). If, for the value D==2 mod 2*3^s, the set
of compatible j is RESTRICTED (e.g. j must be even, or j >= something), that's structure.
More importantly: the trap at level R+j needs D==2 mod 2*3^{R+j-1} -- the FULL order. At the
moment level == R+j (just reached via the j-th zero edge), can D be made ==2 at full precision?

We test a sharper necessary condition. Consider the SIGN bit chain. dlog mod 2 = [c%3==2].
Track how the sign and low-3-adic part evolve with j. Also track the *exact* dlog value
at the working level for SMALL R (so it's enumerable) to directly answer 'is the exact rep 4
reachable', by tracking c mod 3^(R+j) but PRUNING to canonical reps and capping total level.

Strategy here: faithful joint BFS on (j, D_s := dlog mod 2*3^s) with s moderate, then check
the marginal: for each j, which D_s are reachable. Report whether D_s==2 occurs and at which j.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
aS202=1+3**22
import sys; sys.path.insert(0,".")

def build(t):
    M=3**t; N=2*3**(t-1)
    twopow=[1]*N
    for D in range(1,N): twopow[D]=(twopow[D-1]*2)%M
    dl={twopow[D]:D for D in range(N)}
    return M,N,twopow,dl

def joint_bfs(s, R, Qmax, maxstates=5_000_000):
    """track (j, D) with D=dlog mod 2*3^s. Faithful: zero-edge increments j (bounded by Qmax).
       D evolves exactly mod 2*3^s (valid since working level R+j >= s)."""
    M,N,twopow,dl=build(s)
    Ds0 = dl[aS202 % M]
    from collections import deque
    start=(0, Ds0)
    seen={start}; dq=deque([start])
    n=0
    # record marginal: j -> set of D
    while dq and n<maxstates:
        j,D=dq.popleft(); n+=1
        c=twopow[D]
        # one-edges (j unchanged)
        for a in X:
            ta=tau_a(a); Dp=(D-ta)%N; cp=twopow[Dp]
            if cp%9==a and (j,Dp) not in seen:
                seen.add((j,Dp)); dq.append((j,Dp))
        # zero-edges (j+1)
        if j<Qmax:
            base=(3*c+1)%M
            if base%3!=0:
                Db=dl[base]
                for a in X:
                    ta=tau_a(a); Dp=(Db-ta)%N; cp=twopow[Dp]
                    if cp%9==a and (j+1,Dp) not in seen:
                        seen.add((j+1,Dp)); dq.append((j+1,Dp))
    marg={}
    for (j,D) in seen: marg.setdefault(j,set()).add(D)
    return marg, n

# Use R irrelevant to the D-dynamics mod 2*3^s as long as R>=s. Set R=46, Qmax up to 12, s=3.
s=3; M,N,_,_=build(s)
print(f"s={s}: D lives in Z/{N}. trap D==2.")
marg,n=joint_bfs(s, R=46, Qmax=12)
print(f"explored {n} states; reachable D-values per j:")
for j in sorted(marg):
    Ds=marg[j]
    print(f"  j={j:2d}: |D reachable|={len(Ds):4d}/{N}  D==2 in it? {2 in Ds}  full? {len(Ds)==N}")
