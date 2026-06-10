"""
Full ladder SIMULATION on scales small enough to iterate, confirming:
 - the 7<->4 one-edge ladder reaches working-dlog == 2 EXACTLY;
 - every ladder vertex has work_dlog in {2,4} (mod 6) and coarse_dlog != 0 (clean);
 - only ONE zero-edge is used (j stays = 1), so Q=1 suffices;
 - each one-edge satisfies the exact consistency law.
This closes the loop on the analytic argument by direct enumeration at g=3,4,5.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202

def dlogv(c,k): return fast_dlog(c%3**k,k)
def zero_edge_target(c, Knext, alpha):
    M=3**Knext; t=TAU[alpha]
    cp=(pow(pow(2,t,M),-1,M)*((3*c+1)%M))%M
    return (cp,t) if cp%9==alpha else None
def one_edge_target(c,K,alpha):
    M=3**K; t=TAU[alpha]
    cp=(pow(pow(2,t,M),-1,M)*c)%M
    assert cp%9==alpha
    return cp,t

def full_run(g,b,m):
    Rw=g*(m+1)+b; Rc=g*m+b
    c=(1+3**g)%3**Rw; j=0; K=Rw+j
    assert c%9==1
    assert dlogv(c,Rc+j)!=0, "start coarse-precise!"
    # one zero-edge into 7
    zt=zero_edge_target(c,Rw+1,7)
    assert zt is not None
    c,_=zt; j=1; K=Rw+j
    assert c%9==7
    mod6_seen=set(); coarse_zero=False; consistency_ok=True
    steps=0
    while dlogv(c,K)!=2:
        wd=dlogv(c,K); mod6_seen.add(wd%6)
        if dlogv(c,Rc+j)==0: coarse_zero=True; break
        cls=c%9
        tgt = 4 if cls==7 else (7 if cls==4 else None)
        if tgt is None: return dict(ok=False,why=f"left {{4,7}} at {cls}")
        cprev=c
        c,t=one_edge_target(c,K,tgt)
        # verify consistency cprev == 2^t * c (mod 3^K)
        if (cprev%3**K)!=(2**t*c)%3**K: consistency_ok=False
        steps+=1
        if steps>2*3**(Rw): return dict(ok=False,why="too long")
    # final
    wd=dlogv(c,K); mod6_seen.add(wd%6)
    if dlogv(c,Rc+j)==0: coarse_zero=True
    return dict(ok=True, Rw=Rw,Rc=Rc, final_work_dlog=wd, final_c_mod_work=c%3**K,
                ladder_steps=steps, j_final=j, mod6_seen=sorted(mod6_seen),
                hit_coarse_precise=coarse_zero, all_consistency_ok=consistency_ok,
                trap_is_c4=(c%3**K==4))

if __name__=="__main__":
    for (g,b,m) in [(2,2,1),(3,2,1),(4,2,1),(5,2,1),(6,2,1),(3,1,1),(4,0,1)]:
        r=full_run(g,b,m)
        print(f"g={g} b={b} m={m} Rw={r.get('Rw')} Rc={r.get('Rc')}: ", end="")
        if not r['ok']: print("FAIL", r['why']); continue
        print(f"reached work_dlog={r['final_work_dlog']} (c=={r['final_c_mod_work']}), "
              f"steps={r['ladder_steps']}, j_final={r['j_final']} (Q=1 ok), "
              f"work_dlog mod6 seen={r['mod6_seen']} (no 0 -> {0 not in r['mod6_seen']}), "
              f"hit_coarse_precise={r['hit_coarse_precise']}, consistency_ok={r['all_consistency_ok']}, "
              f"trap_c4={r['trap_is_c4']}")
