"""
S241 — The M-FAMILY: does K* (min total kappa to goal) track the cylinder index M?

Faithful geometry for cylinder index M with block width w (real w=22):
   start = 1 + 3^w   (so nu3(start-1) = w = the block width = the gap)
   working level B = M*w + 2 ;  m-precise (forbidden) level R0 = (M-1)*w + 2 = B - w.
   delta_plus(start) at working level = B - w = R0 = (M-1)w + 2  (grows linearly with M).
Barrier claim: every inverse path InvStart(M) -> working-goal has total kappa >= M.

We compute K*_goal = min total kappa to a working-goal, EXACTLY, for small w and M=1..,
with enough zero-budget Q for the minimizer to be realized.  If K*_goal == M for each M, the
barrier holds tightly at the structural level (independent of the astronomically-large real w).

Tractability: modulus 3^(B+Q) = 3^(Mw+2+Q). Keep Mw+2+Q <= ~13.  So small w (2,3) and M up to
~4 with modest Q.  We also report K*_trap (= K*_goal - 1 expected) and the min kappa2 over
mid!=goal splits (device threat).
"""
from collections import deque
ADMISSIBLE=(1,2,4,5,7,8); TAU={1:2,2:1,4:2,5:3,7:4,8:1}
def inv2pow(t,M): return pow(pow(2,t,M),-1,M)
def succ(j,c,B,Q):
    out=[]; M=3**(B+j)
    for a in ADMISSIBLE:
        t=TAU[a]; cp=(inv2pow(t,M)*c)%M
        if cp%9==a: out.append(((j,cp),+1))
    if j<Q:
        M1=3**(B+j+1); val=(3*c+1)%M1
        for a in ADMISSIBLE:
            t=TAU[a]; cp=(inv2pow(t,M1)*val)%M1
            if cp%9==a: out.append(((j+1,cp),-1 if t==1 else 0))
    return out
def spfa(adj,sources,n):
    INF=float('inf'); dist={s:0 for s in sources}; dq=deque(sources); inq=set(sources); cnt={}
    while dq:
        u=dq.popleft(); inq.discard(u); du=dist[u]
        for (v,ka) in adj.get(u,[]):
            if du+ka<dist.get(v,INF):
                dist[v]=du+ka
                if v not in inq:
                    inq.add(v); dq.append(v); cnt[v]=cnt.get(v,0)+1
                    if cnt[v]>n: return dist,True
    return dist,False

def analyse(w,M,Q,max_states=5_000_000):
    R0=(M-1)*w+2; B=M*w+2
    start=(0,(1+3**w)%3**B)
    isg=lambda s: s[1]%3**(B+s[0])==1
    ist=lambda s: s[1]%3**(B+s[0])==4
    forb=lambda s: s[1]%3**(R0+s[0])==1
    adj={}; q=deque([start]); seen={start}; inc=False
    while q:
        if len(seen)>max_states: inc=True; break
        s=q.popleft(); e=succ(*s,B,Q); adj[s]=e
        for (sp,ka) in e:
            if sp not in seen: seen.add(sp); q.append(sp)
    radj={}
    for u in adj:
        for (v,ka) in adj[u]: radj.setdefault(v,[]).append((u,ka))
    goals=[v for v in seen if isg(v) and v[0]>=1]
    traps=[v for v in seen if ist(v) and v[0]>=1]
    df,_=spfa(adj,[start],len(seen))
    db,_=spfa(radj,goals,len(seen)) if goals else ({},False)
    Kg=min((df.get(g,float('inf')) for g in goals),default=None)
    Kt=min((df.get(t,float('inf')) for t in traps),default=None)
    # clean kappa1 (forbidden=sink) for mid!=goal threat
    INF=float('inf'); dc={start:0}; dq=deque([start]); inq={start}; cnt={}
    while dq:
        u=dq.popleft(); inq.discard(u)
        if u!=start and forb(u): continue
        du=dc[u]
        for (v,ka) in adj.get(u,[]):
            if du+ka<dc.get(v,INF):
                dc[v]=du+ka
                if v not in inq:
                    inq.add(v); dq.append(v); cnt[v]=cnt.get(v,0)+1
                    if cnt[v]>len(seen): dq.clear(); break
    threats=[db[v] for v in seen if forb(v) and not isg(v) and v in dc and v in db]
    mink2=min(threats) if threats else None
    return {"w":w,"M":M,"Q":Q,"B":B,"R0":R0,"inc":inc,"n":len(seen),"ngoals":len(goals),
            "Kg":Kg,"Kt":Kt,"mink2_midneqgoal":mink2,"nthreat":len(threats)}

if __name__=="__main__":
    print("M-FAMILY: K*_goal should equal M if the barrier 'kappa>=M' holds tightly.\n")
    print("w=2 (block width analog):")
    for M in [1,2,3,4,5]:
        # choose Q so minimizer realized; bigger M needs bigger Q but modulus 3^(2M+2+Q).
        best=None
        for Q in range(1, 14-(2*M+2)+1 if 14-(2*M+2)+1>1 else 2):
            r=analyse(2,M,Q)
            if r["Kg"] is not None and (best is None or (r["Kg"] is not None and r["Kg"]<best["Kg"])):
                best=r
            if r["inc"]: break
        if best:
            ok = "== M  OK" if best["Kg"]==M else f"!= M  (={best['Kg']})"
            print(f"  M={M}: R0={best['R0']} B={best['B']} bestQ={best['Q']} states={best['n']} "
                  f"K*_goal={best['Kg']} [{ok}]  K*_trap={best['Kt']} "
                  f"min_kappa2(mid!=goal)={best['mink2_midneqgoal']} nthreat={best['nthreat']}")
    print()
    print("w=3:")
    for M in [1,2,3]:
        best=None
        for Q in range(1, 14-(3*M+2)+1 if 14-(3*M+2)+1>1 else 2):
            r=analyse(3,M,Q)
            if r["Kg"] is not None and (best is None or r["Kg"]<best["Kg"]):
                best=r
            if r["inc"]: break
        if best:
            ok = "== M  OK" if best["Kg"]==M else f"!= M  (={best['Kg']})"
            print(f"  M={M}: R0={best['R0']} B={best['B']} bestQ={best['Q']} states={best['n']} "
                  f"K*_goal={best['Kg']} [{ok}]  K*_trap={best['Kt']} "
                  f"min_kappa2(mid!=goal)={best['mink2_midneqgoal']} nthreat={best['nthreat']}")
