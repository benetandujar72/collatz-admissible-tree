"""
S241 — The decisive BARRIER metric on the faithful scaled analog.

We have established (s241_verify_witness / s241_dump_witness): the deep trap c≡4 (dlog=2) IS
clean-reachable, so the canonical-first-split DEVICE (FirstMPrecisionSuffixPositive) is FALSE via
the empty-suffix (mid==goal, kappa2=0) case — BUT those witnessing paths are ALL-ONE-EDGE with
total kappa HUGE (>=34, growing with w), so they do NOT threaten the BARRIER (total kappa >= M).

This script computes the quantity that actually decides the BARRIER:
   K*(M-analog) := min over ALL inverse paths InvStart -> working-goal of the TOTAL kappa.
If K* >= M (=2 for the w<->M=2 analog) the barrier HOLDS outright at this scale.

kappa edges: one-edge +1, tau=1 zero -1, tau>=2 zero 0. Negative edges present => use
Bellman-Ford / SPFA over the EXACT finite reachable graph (state = (j,c) at natural precision).
We also report:
   * min kappa to reach the deep TRAP (c≡4 at working precision),
   * min kappa2 over canonical splits with mid != goal (the real device-threat; 0 splits => the
     ONLY device failures are the harmless empty-suffix ones).
Tractable for w up to ~5 (modulus 3^(2w+2+Q)).
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

def analyse(w,Q,max_states=3_000_000):
    R0,B=w+2,2*w+2
    start=(0,(1+3**w)%3**B)
    isg=lambda s: s[1]%3**(B+s[0])==1
    ist=lambda s: s[1]%3**(B+s[0])==4
    # build full reachable graph
    adj={}; q=deque([start]); seen={start}
    inc=False
    while q:
        if len(seen)>max_states: inc=True; break
        s=q.popleft(); adj[s]=succ(*s,B,Q)
        for (sp,ka) in adj[s]:
            if sp not in seen: seen.add(sp); q.append(sp)
    # SPFA (Bellman-Ford queue) for MIN total kappa from start
    INF=float('inf'); dist={v:INF for v in seen}; dist[start]=0
    inq={start}; dq=deque([start]); cnt={start:0}; neg_cycle=False
    while dq:
        u=dq.popleft(); inq.discard(u)
        du=dist[u]
        for (vv,ka) in adj.get(u,[]):
            if du+ka<dist.get(vv,INF):
                dist[vv]=du+ka
                if vv not in inq:
                    inq.add(vv); dq.append(vv)
                    cnt[vv]=cnt.get(vv,0)+1
                    if cnt[vv]>len(seen):
                        neg_cycle=True; dq.clear(); break
    goals=[v for v in seen if isg(v) and v[0]>=1]
    traps=[v for v in seen if ist(v) and v[0]>=1]
    minK_goal=min((dist[g] for g in goals), default=None)
    minK_trap=min((dist[t] for t in traps), default=None)
    # also MAX? no. report distribution of kappa to goals
    kgoals=sorted({dist[g] for g in goals})
    return {"w":w,"Q":Q,"B":B,"R0":R0,"M_analog":2,"incomplete":inc,"neg_cycle":neg_cycle,
            "n_states":len(seen),"n_goals":len(goals),"n_traps":len(traps),
            "minK_to_goal":minK_goal,"minK_to_trap":minK_trap,"kappa_to_goals":kgoals[:10]}

if __name__=="__main__":
    print("BARRIER metric K* = min total kappa over ALL inverse paths InvStart->goal.")
    print("Analog cylinder index M=2 (w<->22), so barrier HOLDS at this scale iff K* >= 2.\n")
    plan={2:[1,2,3,4,5,6],3:[1,2,3,4],4:[1,2,3],5:[1]}
    for w in plan:
        for Q in plan[w]:
            r=analyse(w,Q)
            inc=" [INC]" if r["incomplete"] else ""
            nc=" [NEG-CYCLE!]" if r["neg_cycle"] else ""
            verdict = ("BARRIER HOLDS (K*>=2)" if (r["minK_to_goal"] is not None and r["minK_to_goal"]>=2)
                       else f"BARRIER THREATENED K*={r['minK_to_goal']}")
            print(f"w={w} Q={Q}: B={r['B']} R0={r['R0']} states={r['n_states']:>7}{inc}{nc} "
                  f"goals={r['n_goals']} K*_goal={r['minK_to_goal']} K*_trap={r['minK_to_trap']} "
                  f"kappa_to_goals={r['kappa_to_goals']}  => {verdict}")
        print()
