"""
RIGOROUS analytic verification of the clean witness (scale-independent core +
O(1) real-scale checks).  No 3^46 iteration.

The clean route from InvStart(m) to the trap (dlog=2 at working precision), avoiding
all coarse-precise vertices:

  STEP A (entry).  Start s0=(j=0, c=aS202 mod 3^Rw), c%9==1 (no one-edge).  Take ONE
    zero-edge with alpha=7 to s1=(j=1, c1) with c1%9==7.  Check: s0,s1 not coarse-precise.

  STEP B (ladder).  At fixed j=1, run one-edges alternating 7->4 (tau=2) and 4->7 (tau=4).
    Per the dlog cocycle (PROVEN), each one-edge target dlog = (source dlog) - tau.
    Starting dlog W:=dlog_{Rw+1}(c1) (== 4 mod 6 since c1==7 mod9 -> 2^4==16==7).
    The ladder visits dlog values  W, W-2, W-6, W-8, W-12, W-14, ...  i.e. {W-6k, W-6k-2}.
    ALL are == 4 or == 2 (mod 6); NONE is == 0 (mod 6).
    Reaches dlog==2 exactly when W-6k-2==2 i.e. k=(W-4)/6 (needs W==4 mod6, W>=4). OK.

  KEY LEMMA (mod-6 shield).  A coarse-precise vertex has coarse-dlog == 0, hence
    coarse-dlog == 0 (mod 6).  Tower compatibility (dlog_reduce, PROVEN):
       coarse-dlog == work-dlog (mod ord(Rc+j))  and a fortiori (mod 6).
    So coarse-dlog == work-dlog (mod 6).  Along the ladder work-dlog in {2,4} mod6 != 0,
    hence coarse-dlog != 0 (mod6), hence NO ladder vertex is coarse-precise.  []

We verify computationally (exact, O(1)):
  - c1%9==7, the zero-edge consistency holds, W:=dlog_{Rw+1}(c1) == 4 mod 6 and W>=4;
  - s0,s1 coarse-dlog != 0;
  - work-dlog == coarse-dlog (mod 6) at s0,s1 (instance of the tower lemma);
  - the trap value: c with dlog==2 at level Rw+jfinal has c==4, and the one-edge
    consistency to the working goal (c==1) holds.
Also verify STEP A entry exists for several scales incl. the real one.
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

def verify_entry(g, b, m):
    Rw=g*(m+1)+b; Rc=g*m+b
    A=1+3**g
    c0=A%3**Rw; j=0
    out={'g':g,'b':b,'m':m,'Rw':Rw,'Rc':Rc}
    out['c0_mod9']=c0%9
    out['c0_coarse_dlog']=dlogv(c0,Rc)            # must != 0 (start not coarse-precise)
    out['c0_work_dlog']=dlogv(c0,Rw)
    out['tower_mod6_s0']=(dlogv(c0,Rc)%6, dlogv(c0,Rw)%6)  # should be equal (tower lemma)
    # zero-edge alpha=7
    zt=zero_edge_target(c0, Rw+1, 7)
    if zt is None:
        # find any zero-edge into {4,7}
        for a in (4,7):
            zt=zero_edge_target(c0, Rw+1, a)
            if zt is not None: break
    if zt is None:
        out['entry']=False; return out
    c1,t=zt
    out['entry']=True; out['zero_alpha']=c1%9; out['zero_tau']=t
    out['c1_mod9']=c1%9
    out['c1_work_dlog_mod6']=dlogv(c1,Rw+1)%6      # should be 4 (c==7)
    out['c1_work_dlog_ge4']=dlogv(c1,Rw+1)>=4
    out['c1_coarse_dlog']=dlogv(c1,Rc+1)           # must != 0
    out['tower_mod6_s1']=(dlogv(c1,Rc+1)%6, dlogv(c1,Rw+1)%6)
    # zero-edge consistency check (exact)
    M=3**(Rw+1)
    out['zero_consistency']=((3*c0+1)%M == (2**t*c1)%M)
    return out

def verify_trap_deepedge(g,b,m,jfinal=1):
    """At working level K=Rw+jfinal, the trap vertex c==4 (dlog 2). Verify a genuine
    one-edge to the working goal (c'==1)."""
    Rw=g*(m+1)+b; K=Rw+jfinal; M=3**K
    c=4 % M
    # one-edge target: c == 2^tau(1)*c' (mod M), c'==1 -> tau(1)=2, c==4*1=4. OK iff c==4.
    cprime=(pow(pow(2,TAU[1],M),-1,M)*c)%M
    return dict(trap_c=c, deep_target_c=cprime, target_is_goal=(cprime%M==1%M),
                target_mod9=cprime%9, tau_used=TAU[1])

if __name__=="__main__":
    print("=== analytic-core verification (exact, O(1)) ===\n")
    print("KEY LEMMA (mod-6 shield): coarse_dlog == work_dlog (mod 6); ladder keeps")
    print("work_dlog in {2,4} mod 6 != 0, so ladder NEVER hits a coarse-precise vertex.\n")
    for (g,b,m) in [(22,2,1),(22,2,2),(2,2,1),(5,2,1),(10,2,1),(30,2,1),(100,2,1)]:
        r=verify_entry(g,b,m)
        print(f"--- g={g} b={b} m={m}: Rw={r['Rw']} Rc={r['Rc']} ---")
        print(f"  start c0%9={r['c0_mod9']} (no one-edge), coarse_dlog(s0)={r['c0_coarse_dlog']} "
              f"(!=0 -> start clean: {r['c0_coarse_dlog']!=0})")
        print(f"  tower mod6 at s0: coarse%6,work%6 = {r['tower_mod6_s0']} (equal -> {r['tower_mod6_s0'][0]==r['tower_mod6_s0'][1]})")
        if not r.get('entry'):
            print("  ENTRY zero-edge into {4,7}: NONE -> recipe blocked here"); continue
        print(f"  entry zero-edge -> c1%9={r['c1_mod9']} (tau={r['zero_tau']}), consistency={r['zero_consistency']}")
        print(f"  c1 work_dlog %6 = {r['c1_work_dlog_mod6']} (==4 -> {r['c1_work_dlog_mod6']==4}), "
              f">=4: {r['c1_work_dlog_ge4']}; coarse_dlog(s1)={r['c1_coarse_dlog']} "
              f"(!=0 -> {r['c1_coarse_dlog']!=0})")
        print(f"  tower mod6 at s1: {r['tower_mod6_s1']} (equal -> {r['tower_mod6_s1'][0]==r['tower_mod6_s1'][1]})")
        d=verify_trap_deepedge(g,b,m,jfinal=1)
        print(f"  trap deep one-edge: trap c={d['trap_c']} --one(tau={d['tau_used']})--> "
              f"c'={d['deep_target_c']} (goal? {d['target_is_goal']})")
