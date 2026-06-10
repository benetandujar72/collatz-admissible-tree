"""
B1 -- The dlog-space dynamics. Track D = dlog of the representative, as the path evolves.

We work at a FIXED truncation level t (so D lives in Z/(2*3^{t-1})), using dlog_reduce to
keep D consistent across levels. This is EXACT for the low t digits as long as the actual
working level R+j >= t (always, R>=46).

Edge action on (j, c) in dlog coordinates D = dlog_t(c mod 3^t):
  one-edge (alpha admissible, tau=tau(alpha)): c' = 2^{-tau} c, so dlog(c') = dlog(c) - tau.
     Admissibility c'%9==alpha couples to the low 2 digits of c'. We MUST track c mod 9 too
     (equivalently D mod ord(2 mod 9)=6, since dlog_2 determines c mod 9). Actually c mod 3^t
     is fully recovered from D=dlog_t(c) (2 primitive root). So track D; c mod 9 = 2^D mod 9;
     admissibility c'%9==alpha <=> 2^{D-tau} % 9 == alpha.
  zero-edge: c' = 2^{-tau}(3c+1). In dlog: dlog(c') = dlog(3c+1) - tau. dlog(3c+1) is the
     'affine jump' -- NOT linear in D. We compute it directly: from D recover c mod 3^t = 2^D,
     form 3c+1 mod 3^t, take its dlog. This is exact at level t.

So the dlog-space state is just D in Z/(2*3^{t-1}); transitions are computable. BFS over D.
This is EXACTLY the projection of the real dynamics (faithful), and finite (size 2*3^{t-1}).

We confirm Reach in D-space = all D (consistent with Reach_t=units), THEN study the
j-COUPLING: track (D, j mod p) to see if dlog=2 requires a specific j-residue. If reaching
D==2 forces j into a class incompatible with 'j small / level just reached', that's an obstruction.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
aS202=1+3**22

def build(t):
    M=3**t
    N=2*3**(t-1)  # order of 2 mod 3^t
    # precompute 2^D mod M for all D
    twopow=[1]*(N)
    for D in range(1,N): twopow[D]=(twopow[D-1]*2)%M
    # dlog table: residue -> D
    dl={}
    for D in range(N): dl[twopow[D]]=D
    inv2=(M+1)//2
    return M,N,twopow,dl,inv2

def transitions(t):
    """return function step(D)->list of (D', kind, tau) over dlog states, faithful mod 3^t."""
    M,N,twopow,dl,inv2=build(t)
    def step(D):
        out=[]
        c=twopow[D]
        # one-edges: c'=2^{-tau}c, dlog'=D-tau mod N; admissible if c'%9==alpha
        for a in X:
            ta=tau_a(a)
            Dp=(D-ta)%N
            cp=twopow[Dp]
            if cp%9==a:
                out.append((Dp,'one',ta))
        # zero-edges: c'=2^{-tau}(3c+1); dlog(3c+1) then minus tau
        base=(3*c+1)%M
        if base%3!=0:
            Db=dl[base]
            for a in X:
                ta=tau_a(a)
                Dp=(Db-ta)%N
                cp=twopow[Dp]
                if cp%9==a:
                    out.append((Dp,'zero',ta))
        return out
    return step,N,dl,twopow

def D_start(t):
    M=3**t
    a=aS202%M
    _,_,_,dl,_=build(t)
    return dl[a]

print("=== dlog-space reachability (faithful mod 3^t), is D=2 (trap) reachable? ===")
for t in range(2,10):
    step,N,dl,twopow=transitions(t)
    Ds=D_start(t)
    seen={Ds}; fr=[Ds]
    while fr:
        nf=[]
        for D in fr:
            for (Dp,k,ta) in step(D):
                if Dp not in seen: seen.add(Dp); nf.append(Dp)
        fr=nf
    print(f"t={t}: start D={Ds}, |reach D|={len(seen)} of N={N}; D==2 reachable? {2 in seen}; all? {len(seen)==N}")
