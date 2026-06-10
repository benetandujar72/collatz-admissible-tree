"""Dump ONE explicit clean goal-witness (w small) with full edge labels, and AUDIT it:
verify every interior vertex is NOT coarse-m-precise (c!=1 mod 3^(R0+j)), the last vertex is a
working-goal (c==1 mod 3^(B+j)), the penultimate is the deep trap (c==4 mod 3^(B+j)) reached by a
tau=2 one-edge, and report the kappa profile.  This audits that 'empty-suffix device death' is a
GENUINE clean threading, not an artifact of the sink construction."""
from collections import deque
ADMISSIBLE=(1,2,4,5,7,8); TAU={1:2,2:1,4:2,5:3,7:4,8:1}
def inv2pow(t,M): return pow(pow(2,t,M),-1,M)
def succ(j,c,B,Q):
    out=[]; M=3**(B+j)
    for a in ADMISSIBLE:
        t=TAU[a]; cp=(inv2pow(t,M)*c)%M
        if cp%9==a: out.append((j,cp,'one',t,+1))
    if j<Q:
        M1=3**(B+j+1); val=(3*c+1)%M1
        for a in ADMISSIBLE:
            t=TAU[a]; cp=(inv2pow(t,M1)*val)%M1
            if cp%9==a: out.append((j+1,cp,'zero',t,-1 if t==1 else 0))
    return out

def run(w,Q):
    R0,B=w+2,2*w+2
    start=(0,(1+3**w)%3**B)
    forb=lambda s: s[1]%3**(R0+s[0])==1
    isg=lambda s: s[1]%3**(B+s[0])==1
    ist=lambda s: s[1]%3**(B+s[0])==4
    assert not forb(start)
    par={start:(None,None,None,0)}; q=deque([start]); goal=None
    while q:
        s=q.popleft()
        if isg(s) and s[0]>=1: goal=s; break
        if s!=start and forb(s): continue
        for (jp,cp,kind,t,ka) in succ(*s,B,Q):
            sp=(jp,cp)
            if sp not in par: par[sp]=(s,kind,t,ka); q.append(sp)
    if goal is None: print(f"w={w} Q={Q}: no clean goal"); return
    # reconstruct
    seq=[]; cur=goal
    while cur is not None:
        prev,kind,t,ka=par[cur]; seq.append((cur,kind,t,ka)); cur=prev
    seq=list(reversed(seq))
    # audit
    n=len(seq)
    interior_clean = all(not forb(seq[i][0]) for i in range(n-1))  # all but the goal
    last=seq[-1][0]; penult=seq[-2][0] if n>=2 else None
    last_goal=isg(last); penult_trap=ist(penult) if penult else None
    final_edge=seq[-1][1:]  # (kind,tau,kappa) into goal
    kappa_total=sum(s[3] for s in seq)
    print(f"=== w={w} Q={Q}  B={B} R0={R0}  path length={n-1} edges ===")
    print(f"  start={start}  goal={goal}")
    print(f"  interior all NON-coarse-precise (clean)? {interior_clean}")
    print(f"  last is working-goal (c==1 mod 3^(B+j))? {last_goal}")
    print(f"  penultimate is deep trap (c==4 mod 3^(B+j))? {penult_trap}")
    print(f"  final edge into goal (kind,tau,kappa): {final_edge}")
    print(f"  total kappa along path = {kappa_total}")
    # show edge-kind histogram and first/last few labeled steps
    kinds=[s[1] for s in seq[1:]]
    print(f"  edge kinds: one={kinds.count('one')} zero={kinds.count('zero')}")
    print(f"  last 4 steps (vertex,kind,tau,kappa):")
    for s in seq[-4:]:
        v=s[0]
        print(f"     j={v[0]} c={v[1]} (c mod9={v[1]%9}, c mod 3^(R0+j)={v[1]%3**(R0+v[0])}, "
              f"c mod 3^(B+j)={v[1]%3**(B+v[0])})  edge={s[1]},tau={s[2]},kappa={s[3]}")

for (w,Q) in [(2,1),(2,2),(3,1),(4,1)]:
    run(w,Q); print()
