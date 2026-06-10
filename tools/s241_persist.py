"""
S241 — THE decisive test: does the empty-suffix device-refutation PERSIST as block width w grows?

A clean kappa-path InvStart -> working-goal with NO m-precise interior vertex (mid==goal,
kappa2=0) REFUTES FirstMPrecisionSuffixPositive.  We established it exists for the M=2 analog at
w=2..5.  The orbit-length heuristic suggests that as the gap g=B-R0=w grows, the unique fine-goal
gets ~3^w coarse-m-precise points 'in front of it', which COULD force the first m-precise vertex to
precede the goal (mid!=goal), nullifying the refutation.  Branching freedom fights this.  Only the
EXACT computation decides.

For the M=2 analog (R0=w+2, B=2w+2) we compute, for w=2..wmax and the cheapest budget Q=1
(single zero-edge, then one-edges at j=1 — the tightest, hardest case for a clean goal):
  * EXISTS a clean working-goal (empty-suffix counterexample)?  -> device refuted at this w.
  * If yes: the path length and #one-edges (orbit length used).
  * The number of m-precise (coarse c≡1 mod 3^(R0+1)) vertices that are CLEAN-reachable but are
    NOT goals and lie before any goal (potential mid!=goal alternatives).
We push wmax as far as the j=1 modulus 3^(B+1)=3^(2w+3) allows exhaustive BFS (w<=5 -> 3^13).
We ALSO run Q=0-ish variants and report the trend in 'does a clean goal exist'.
"""
from collections import deque
ADM=(1,2,4,5,7,8); TAU={1:2,2:1,4:2,5:3,7:4,8:1}
def inv2(t,M): return pow(pow(2,t,M),-1,M)
def succ(j,c,B,Q):
    out=[]; M=3**(B+j)
    for a in ADM:
        t=TAU[a]; cp=(inv2(t,M)*c)%M
        if cp%9==a: out.append(((j,cp),1,'one',t))
    if j<Q:
        M1=3**(B+j+1); val=(3*c+1)%M1
        for a in ADM:
            t=TAU[a]; cp=(inv2(t,M1)*val)%M1
            if cp%9==a: out.append(((j+1,cp),-1 if t==1 else 0,'zero',t))
    return out

def clean_goal_exists(w,Q,cap=8_000_000):
    R0,B=w+2,2*w+2
    start=(0,(1+3**w)%3**B)
    forb=lambda s: s[1]%3**(R0+s[0])==1
    isg=lambda s: s[1]%3**(B+s[0])==1 and s[0]>=1
    assert not forb(start)
    # clean BFS (forbidden = sink). Find any working-goal; record path length.
    par={start:(None,0)}; q=deque([start]); inc=False
    goal=None
    n_mprec_clean=0
    while q:
        if len(par)>cap: inc=True; break
        s=q.popleft()
        if isg(s):
            goal=s; break
        if s!=start and forb(s):
            n_mprec_clean+=1
            continue
        for (sp,ka,kind,t) in succ(*s,B,Q):
            if sp not in par: par[sp]=(s,par[s][1]+1); q.append(sp)
    plen=None
    if goal is not None:
        # length
        cur=goal; L=0
        while par[cur][0] is not None: cur=par[cur][0]; L+=1
        plen=L
    return {"w":w,"Q":Q,"R0":R0,"B":B,"clean_goal_exists":goal is not None,
            "path_len":plen,"states":len(par),"inc":inc,
            "n_mprec_clean_before":n_mprec_clean}

if __name__=="__main__":
    print("DOES the empty-suffix device-refutation (clean goal, mid==goal) PERSIST as w grows?")
    print("M=2 analog (R0=w+2, B=2w+2). 'clean_goal_exists=True' => device REFUTED at that w.\n")
    for Q in [1,2,3]:
        print(f"--- budget Q={Q} ---")
        for w in range(2,7):
            # tractability: clean BFS visits up to ~3^(B+Q)=3^(2w+2+Q); cap by skipping big ones
            if (2*w+2+Q) > 14:
                print(f"  w={w}: SKIP (modulus 3^{2*w+2+Q} too large)"); continue
            r=clean_goal_exists(w,Q)
            inc=" [INC]" if r["inc"] else ""
            print(f"  w={w}: R0={r['R0']} B={r['B']} clean_goal_exists={r['clean_goal_exists']} "
                  f"path_len={r['path_len']} states={r['states']}{inc} "
                  f"(#m-precise clean-reached as leaves={r['n_mprec_clean_before']})")
        print()
