"""
Extract an ACTUAL clean witness path: from InvStart, a sequence of admissible
inverse edges reaching the WORKING trap (working-dlog == 2, i.e. c==4 at working
full precision -> can deep-jump to working goal) WITHOUT any intermediate vertex
being coarse-precise (coarse-dlog==0).  Done at full precision (small scaled model).

Then we VERIFY the witness independently: each edge satisfies the exact Lean
consistency law; no intermediate vertex is coarse-precise; the final vertex is the
trap; and there is a genuine deep one-edge from the trap to the working goal.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X
from collections import deque

def dlogv(c,k): return fast_dlog(c%3**k,k)
def ordk(k): return 2*3**(k-1)

def edges_full(Rw,Q,j,c):
    out=[]; M=3**(Rw+j)
    for a in sorted(X):
        t=TAU[a]; inv=pow(pow(2,t,M),-1,M); cp=(inv*c)%M
        if cp%9==a: out.append((j,cp,t,'one',a))
    if j<Q:
        Mp=3**(Rw+j+1)
        for a in sorted(X):
            t=TAU[a]; inv=pow(pow(2,t,Mp),-1,Mp); cp=(inv*((3*c+1)%Mp))%Mp
            if cp%9==a: out.append((j+1,cp,t-2,'zero',a))
    return out

def find_clean_witness(g,b,Q,m=1,max_states=2_000_000):
    Rw=g*(m+1)+b; Rc=g*m+b; A=1+3**g
    c0=A%3**Rw
    def coarse_d(j,c): return dlogv(c, Rc+j)
    def work_d(j,c): return dlogv(c, Rw+j)
    start_flag=(coarse_d(0,c0)==0)
    # BFS with parent pointers, state (j,c,flag)
    start=(0,c0,start_flag)
    parent={start:None}
    dq=deque([start]); n=0
    target=None
    while dq and n<max_states:
        st=dq.popleft(); n+=1
        j,c,flag=st
        if (not flag) and work_d(j,c)==2:
            target=st; break
        for (j2,c2,om,kind,a) in edges_full(Rw,Q,j,c):
            cd2=coarse_d(j2,c2); f2=flag or (cd2==0)
            ns=(j2,c2,f2)
            if ns not in parent:
                parent[ns]=(st,(kind,om,a))
                dq.append(ns)
    if target is None: return None
    # reconstruct
    path=[]; st=target
    while parent[st] is not None:
        prev,einfo=parent[st]
        path.append((prev,einfo,st)); st=prev
    path.reverse()
    return dict(Rw=Rw,Rc=Rc,c0=c0,path=path,target=target)

def verify_witness(g,b,Q,w):
    Rw,Rc=w['Rw'],w['Rc']
    ok=True; msgs=[]
    # check start not coarse-precise
    j0,c0,_=([w['path'][0][0]]+[None])[0], None, None
    (sj,sc,sflag)=w['path'][0][0]
    if dlogv(sc,Rc+sj)==0:
        ok=False; msgs.append("start IS coarse-precise (bad)")
    for (prev,(kind,om,a),nxt) in w['path']:
        pj,pc,pf=prev; nj,nc,nf=nxt
        Mn=3**(Rw+nj)
        if kind=='one':
            assert nj==pj
            lhs=pc%Mn; rhs=(2**TAU[a]*nc)%Mn
            if lhs!=rhs: ok=False; msgs.append(f"one-edge consistency FAIL at {prev}->{nxt}")
        else:
            assert nj==pj+1
            lhs=(3*pc+1)%Mn; rhs=(2**TAU[a]*nc)%Mn
            if lhs!=rhs: ok=False; msgs.append(f"zero-edge consistency FAIL at {prev}->{nxt}")
        if nc%9!=a: ok=False; msgs.append(f"target class FAIL at {nxt}")
        # intermediate (non-final) coarse-precise check
        if nxt!=w['target']:
            if dlogv(nc,Rc+nj)==0:
                ok=False; msgs.append(f"intermediate coarse-precise at {nxt} (violates clean)")
    # final = trap: work-dlog==2
    tj,tc,tf=w['target']
    if dlogv(tc,Rw+tj)!=2: ok=False; msgs.append("final not working-trap")
    # genuine deep one-edge trap -> working goal
    Mt=3**(Rw+tj)
    # goal v'.c==1; one-edge consistency tc == 2^tau(1)*1 == 4
    if tc%Mt != 4%Mt: ok=False; msgs.append(f"trap c != 4 mod working (c%Mt={tc%Mt})")
    return ok,msgs

if __name__=="__main__":
    for (g,b,Q) in [(2,2,2),(3,2,2),(2,1,2),(2,3,2)]:
        w=find_clean_witness(g,b,Q,m=1,max_states=1_500_000)
        print(f"\n=== g={g} b={b} Q={Q}: Rw={g*2+b} Rc={g+b} ===")
        if w is None:
            print("  NO clean witness found (within budget).")
            continue
        ok,msgs=verify_witness(g,b,Q,w)
        print(f"  clean witness length = {len(w['path'])} edges; VERIFIED={ok}")
        if msgs: print("   issues:", msgs)
        # print the path compactly
        sj,sc,_=w['path'][0][0]
        print(f"  start (j={sj}, c={sc}, c%9={sc%9}, coarse_dlog={dlogv(sc,w['Rc']+sj)}, work_dlog={dlogv(sc,w['Rw']+sj)})")
        for (prev,(kind,om,a),nxt) in w['path']:
            nj,nc,nf=nxt
            print(f"    --{kind}(alpha={a},w={om})--> (j={nj}, c={nc}, c%9={nc%9}, "
                  f"cdlog={dlogv(nc,w['Rc']+nj)}, wdlog={dlogv(nc,w['Rw']+nj)}, dirty={nf})")
