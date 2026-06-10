"""
CONSTRUCTIVE clean witness at REAL scale, following the analytic recipe:
  (1) start c0 = aS202 mod 3^Rw (c==1 mod9, no one-edge).
  (2) ONE zero-edge into the {4,7} mod-9 orbit (choose alpha=7 -> c'==7 mod9).
  (3) pure one-edge LADDER at fixed j: 7->4 (tau2) ->7 (tau4) -> ... decrement dlog
      by 2,4,2,4,...  staying in dlog ==2 or 4 (mod 6), down to dlog==2 (the trap).
We CHECK at every step:
  - edge consistency (exact Lean law) at working precision 3^(Rw+j);
  - the vertex is NEVER coarse-precise (coarse-dlog at level Rc+j != 0);
  - the final vertex has working-dlog==2 (c==4 mod 3^Rw+j) -> deep one-edge to working goal.

The ladder works at fixed j IF, after the single zero-edge, the working dlog at that j
is ==4 mod 6 and >= 4.  We pick the zero-edge target to land c==7 (dlog==4 mod6) and
verify the value is large; then ladder to 2.  If the single-j ladder cannot reach 2
because of cyclic-group size (it can: the value just decreases by 2 each effective pair),
we confirm by simulation.

Real scale: residual m=1 -> Rw=46, Rc=24.  Also test m=2 (Rw=68,Rc=46) and big synthetic.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202

def dlogv(c,k): return fast_dlog(c%3**k,k)

def one_edge_target(c, K, alpha):
    """target c' with c == 2^tau(alpha)*c' (mod 3^K), c'%9==alpha (must hold)."""
    M=3**K; t=TAU[alpha]
    cp=(pow(pow(2,t,M),-1,M)*c)%M
    assert cp%9==alpha, (c%9, alpha, cp%9)
    return cp,t

def zero_edge_target(c, Knext, alpha):
    """from c (level Kprev=Knext-1) to c' (level Knext): 3c+1==2^tau*c' (mod 3^Knext)."""
    M=3**Knext; t=TAU[alpha]
    cp=(pow(pow(2,t,M),-1,M)*((3*c+1)%M))%M
    if cp%9!=alpha: return None
    return cp,t

def build(g, b, m=1, verbose=False):
    Rw=g*(m+1)+b; Rc=g*m+b
    A=1+3**g
    c=A%3**Rw; j=0
    K=Rw+j
    assert c%9==1, c%9
    log=[]
    def coarse_dlog(j,c): return dlogv(c, Rc+j)
    def work_dlog(j,c): return dlogv(c, Rw+j)
    # record start
    if coarse_dlog(j,c)==0:
        return dict(ok=False, why="start is coarse-precise")
    log.append(('start',j,c,c%9,coarse_dlog(j,c),work_dlog(j,c)))
    # (2) zero-edge with alpha=7  (need it to be admissible)
    zt=zero_edge_target(c, Rw+j+1, 7)
    if zt is None:
        # try other alphas to enter {4,7}
        for a in [4,7,1,2,5,8]:
            zt=zero_edge_target(c, Rw+j+1, a)
            if zt is not None and zt[0]%9 in (4,7): break
        if zt is None: return dict(ok=False, why="no zero-edge into {4,7}")
    c,_=zt; j=j+1; K=Rw+j
    if coarse_dlog(j,c)==0: return dict(ok=False, why="post-zero-edge coarse-precise")
    log.append(('zero',j,c,c%9, coarse_dlog(j,c), work_dlog(j,c)))
    # (3) ladder to working-dlog == 2
    steps=0; maxsteps=10*3**(Rw+j)  # safety
    while work_dlog(j,c)!=2:
        wd=work_dlog(j,c)
        cls=c%9
        # choose the one-edge that keeps us in {4,7} and decreases dlog
        if cls==7:
            tgt=4  # 7->4 : dlog -2
        elif cls==4:
            tgt=7  # 4->7 : dlog -4
        elif cls==1:
            # we accidentally hit c==1 (dlog==0 mod6) -> would be near precise; avoid.
            return dict(ok=False, why=f"ladder hit c==1 mod9 at wdlog={wd}", log=log)
        else:
            return dict(ok=False, why=f"ladder left {{4,7}} at c%9={cls}, wdlog={wd}", log=log)
        cp,t=one_edge_target(c, K, tgt)
        c=cp
        if coarse_dlog(j,c)==0:
            return dict(ok=False, why=f"ladder hit coarse-precise at wdlog={work_dlog(j,c)}", log=log)
        steps+=1
        if steps>maxsteps: return dict(ok=False, why="ladder did not terminate", log=log)
    log.append(('trap',j,c,c%9, coarse_dlog(j,c), work_dlog(j,c)))
    # verify deep one-edge trap->working goal: c==4 mod 3^(Rw+j)
    M=3**(Rw+j)
    deepok=(c%M==4%M)
    return dict(ok=True, Rw=Rw, Rc=Rc, ladder_steps=steps, final_j=j,
                deep_one_edge_ok=deepok, log=log)

if __name__=="__main__":
    cases=[(22,2,1),(22,2,2),(2,2,1),(3,2,1),(5,2,1),(10,2,1),(30,2,1),(50,2,1)]
    for (g,b,m) in cases:
        r=build(g,b,m)
        print(f"\n=== g={g} b={b} m={m}  (Rw={g*(m+1)+b}, Rc={g*m+b}) ===")
        if not r['ok']:
            print(f"  BLOCKED: {r['why']}")
            if 'log' in r:
                for e in r['log'][-4:]: print("   ", e)
            continue
        print(f"  CLEAN WITNESS BUILT: ladder_steps={r['ladder_steps']}, final_j={r['final_j']}, "
              f"deep_one_edge_to_goal_OK={r['deep_one_edge_ok']}")
        print(f"  trace (kind,j,c%9,coarse_dlog,work_dlog):")
        for e in r['log']:
            kind,j,c,c9,cd,wd=e
            print(f"    {kind:5s} j={j} c%9={c9} cdlog={cd} wdlog={wd}")
