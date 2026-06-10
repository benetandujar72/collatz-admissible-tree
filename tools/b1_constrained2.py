"""
B1 -- Constrained trap reachability, FAITHFUL regime r > g (real: r=24, g=22).

Real structure (the (m+1)=M barrier):
  R = 22M+2.  trap level = R+j.  coarse-m-precise level = R-22+j = 22(M-1)+2+j.
  Let r := R-22 = 22(M-1)+2  (>= 24 for M>=2, i.e. m>=1),  g := 22 (fixed window).
  So r=24,46,... and g=22 ALWAYS, hence r > g (r-g = 22(M-2)+24 >= ... for M=2: r=24,g=22, r>g by 2).
  start c0 = aS202 mod 3^R = aS202 mod 3^(r+g). aS202 = 1+3^22 = 1+3^g.
    start precise? c0 mod 3^r == 1?  c0 = (1+3^g) mod 3^(r+g). Since g < r, 3^g < 3^r, so
    c0 mod 3^r = 1+3^g != 1 (g>=1).  => start NOT precise. GOOD (matches Lean).

To enumerate, shrink with r > g, e.g. (r,g) in {(3,2),(4,2),(4,3),(5,2),(5,3),(5,4),(6,4),(7,5)}.
trap = c==4 at level r+g+j. precise = c==1 mod 3^(r+j). Constrained BFS does not expand precise.
We also EXTRACT an explicit constrained path and verify no intermediate vertex is precise.
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
from collections import deque

def run(r, g, levelcap, statecap=5_000_000):
    assert g < r
    base_level=r+g
    c0=(1+3**g) % 3**base_level
    start=(0,c0)
    def precise(j,c): return c % 3**(r+j) == 1
    def trap(j,c): return c==4
    assert not precise(0,c0), "start should be non-precise in faithful regime"
    # constrained BFS with parent tracking for path extraction
    parent={start:None}; dq=deque([start]); found=None
    while dq and len(parent)<statecap:
        j,c=dq.popleft(); L=base_level+j
        if trap(j,c): found=(j,c); break
        if precise(j,c): continue
        M=3**L; inv2=(M+1)//2
        for a in X:
            cp=(pow(inv2,tau_a(a),M)*c)%M
            if cp%9==a and (j,cp) not in parent:
                parent[(j,cp)]=((j,c),('one',a)); dq.append((j,cp))
        if j+1<=levelcap:
            Mp=3**(L+1); inv2p=(Mp+1)//2
            bb=(3*c+1)%Mp
            for a in X:
                cp=(pow(inv2p,tau_a(a),Mp)*bb)%Mp
                if cp%9==a and (j+1,cp) not in parent:
                    parent[(j+1,cp)]=((j,c),('zero',a)); dq.append((j+1,cp))
    if found is None:
        return None, len(parent)
    # reconstruct
    path=[]; node=found
    while node is not None:
        path.append(node); pe=parent[node]; node=pe[0] if pe else None
    path.reverse()
    # verify no intermediate (excluding the trap endpoint) is precise
    bad=[v for v in path[:-1] if precise(*v)]
    return (found, path, bad, len(parent))

print("=== FAITHFUL constrained trap reachability (r>g) ===")
for r,g in [(3,2),(4,2),(4,3),(5,2),(5,3),(5,4),(6,4),(7,5),(8,6)]:
    res=run(r,g, levelcap=g+5)
    if res[0] is None:
        print(f"  r={r} g={g}: trap NOT reachable (constrained) in {res[1]} states")
    else:
        found,path,bad,ns=res
        print(f"  r={r} g={g}: TRAP reached at {found} via {len(path)-1} edges, "
              f"precise vertices on path (excl. endpoint): {len(bad)}  states={ns}")
        if r==4 and g==3:
            print("    explicit path:", [(j,c) for (j,c) in path])
            for i in range(1,len(path)):
                print("      edge", path[i-1], "->", path[i])
