"""
S241 — FINAL decisive metrics on the faithful scaled analog.

(1) Push w=2 to large Q (B=6 cheap): does K*_to_goal (min total kappa) stay >= M=2, i.e. is the
    barrier exactly TIGHT (=2) and never broken?  Also K*_to_trap.
(2) The TRUE device-threat: min over canonical splits (mid = first m-precise vertex on a
    start->goal path, allowing the path to PASS THROUGH m-precise vertices) of kappa2 = kappa
    on the suffix mid..goal, INCLUDING the binding case mid != goal.  Computed exactly:
    kappa2(path) = total_kappa(path) - kappa(prefix start..mid). We compute, for the
    kappa-MINIMIZING start->goal structure, the min kappa2 with mid != goal.
    Method: min kappa1 to each m-precise vertex v (Bellman-Ford), and min kappa2 from each
    m-precise v to a goal (Bellman-Ford on reverse graph); a split exists with
    kappa2 = (min kappa2 from v to goal) for any reachable m-precise v that lies on some
    start->goal path.  We report min over m-precise v (v != any goal) of [minkappa2 v->goal],
    and whether such v is actually the FIRST m-precise on a realizing path (sufficient: v
    reachable from start by a path with NO earlier m-precise vertex -> use the clean-tree
    kappa1).  This is the exact device-failure test for mid != goal.

(3) Cross-check at w=3.
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

def spfa(adj, sources, nstates):
    INF=float('inf'); dist={};
    for s in sources: dist[s]=0
    dq=deque(sources); inq=set(sources); cnt={}
    while dq:
        u=dq.popleft(); inq.discard(u); du=dist[u]
        for (vv,ka) in adj.get(u,[]):
            if du+ka<dist.get(vv,INF):
                dist[vv]=du+ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv]=cnt.get(vv,0)+1
                    if cnt[vv]>nstates: return dist, True
    return dist, False

def analyse(w,Q,max_states=6_000_000):
    R0,B=w+2,2*w+2
    start=(0,(1+3**w)%3**B)
    isg=lambda s: s[1]%3**(B+s[0])==1
    ist=lambda s: s[1]%3**(B+s[0])==4
    forb=lambda s: s[1]%3**(R0+s[0])==1   # m-precise
    # forward graph
    adj={}; q=deque([start]); seen={start}; inc=False
    while q:
        if len(seen)>max_states: inc=True; break
        s=q.popleft(); e=succ(*s,B,Q); adj[s]=e
        for (sp,ka) in e:
            if sp not in seen: seen.add(sp); q.append(sp)
    # reverse graph
    radj={}
    for u in adj:
        for (vv,ka) in adj[u]:
            radj.setdefault(vv,[]).append((u,ka))
    goals=[v for v in seen if isg(v) and v[0]>=1]
    traps=[v for v in seen if ist(v) and v[0]>=1]
    # min total kappa start->*
    dist_f,_=spfa(adj,[start],len(seen))
    minK_goal=min((dist_f.get(g,float('inf')) for g in goals), default=None)
    minK_trap=min((dist_f.get(t,float('inf')) for t in traps), default=None)
    # min kappa2 from each vertex to a goal: SPFA on reverse graph from all goals
    dist_b,_=spfa(radj,goals,len(seen))   # dist_b[v] = min kappa from v to some goal
    # clean kappa1: min total kappa start->v with NO m-precise interior (forbidden = sink)
    cadj={u:adj[u] for u in adj}
    # clean SPFA: do not RELAX OUT of forbidden vertices (treat as sinks) except start
    INF=float('inf'); dist_c={start:0}; dq=deque([start]); inq={start}; cnt={}
    while dq:
        u=dq.popleft(); inq.discard(u)
        if u!=start and forb(u): continue
        du=dist_c[u]
        for (vv,ka) in adj.get(u,[]):
            if du+ka<dist_c.get(vv,INF):
                dist_c[vv]=du+ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv); cnt[vv]=cnt.get(vv,0)+1
                    if cnt[vv]>len(seen): dq.clear(); break
    # device failure mid!=goal: an m-precise vertex v (NOT a goal) that is clean-reachable from
    # start (dist_c finite) AND can reach a goal (dist_b finite) with kappa2 = dist_b[v] <= 0.
    threats=[]
    for v in seen:
        if forb(v) and not isg(v) and v in dist_c and v in dist_b:
            k2=dist_b[v]
            threats.append((k2, dist_c[v], v))
    threats.sort()
    min_k2_midneqgoal = threats[0][0] if threats else None
    # also: overall min kappa2 over ALL m-precise v (incl goals=empty suffix gives 0)
    return {"w":w,"Q":Q,"B":B,"R0":R0,"incomplete":inc,
            "n_states":len(seen),"n_goals":len(goals),
            "minK_goal":minK_goal,"minK_trap":minK_trap,
            "min_kappa2_midneqgoal":min_k2_midneqgoal,
            "n_threats_midneqgoal":len(threats),
            "worst_threats":threats[:5]}

if __name__=="__main__":
    print("(1)+(2) w=2 pushed to large Q (barrier tightness + true device threat mid!=goal):")
    for Q in [1,2,3,4,5,6,7,8,9,10]:
        r=analyse(2,Q)
        inc=" [INC]" if r["incomplete"] else ""
        print(f"  w=2 Q={Q:>2}: states={r['n_states']:>8}{inc} goals={r['n_goals']:>2} "
              f"K*_goal={r['minK_goal']} K*_trap={r['minK_trap']} "
              f"min_kappa2(mid!=goal)={r['min_kappa2_midneqgoal']} "
              f"n_midneqgoal_mprecise={r['n_threats_midneqgoal']}")
    print()
    print("(3) w=3 cross-check:")
    for Q in [1,2,3,4]:
        r=analyse(3,Q)
        inc=" [INC]" if r["incomplete"] else ""
        print(f"  w=3 Q={Q:>2}: states={r['n_states']:>8}{inc} goals={r['n_goals']:>2} "
              f"K*_goal={r['minK_goal']} K*_trap={r['minK_trap']} "
              f"min_kappa2(mid!=goal)={r['min_kappa2_midneqgoal']} "
              f"n_midneqgoal_mprecise={r['n_threats_midneqgoal']}")
    print()
    print("(4) w=4 cross-check:")
    for Q in [1,2,3]:
        r=analyse(4,Q)
        inc=" [INC]" if r["incomplete"] else ""
        print(f"  w=4 Q={Q:>2}: states={r['n_states']:>8}{inc} goals={r['n_goals']:>2} "
              f"K*_goal={r['minK_goal']} K*_trap={r['minK_trap']} "
              f"min_kappa2(mid!=goal)={r['min_kappa2_midneqgoal']} "
              f"n_midneqgoal_mprecise={r['n_threats_midneqgoal']}")
