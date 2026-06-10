"""
B1 -- The genuine subtlety: within the ONE-EDGE orbit at a fixed level (fixed j), can we reach
c=4 from c7 WITHOUT passing through an m-precise vertex (c == 1 mod 3^(r+j))?

At fixed j, the one-edge subgraph on units is (proved) the full <2>-orbit = all units. The
m-precise vertices at this level are those with c == 1 mod 3^(r+j): a sub-cylinder. We must check
the one-edge graph MINUS the precise vertices still connects c7 (the entry) to c4 (the trap).

But note: a one-edge is c -> 2^{-tau} c (admissible). The PRECISE vertices c==1 mod 3^(r+j) are a
coset. Removing them: is c4 still reachable from c7? We test in faithful small model (r>g, fixed j=1
i.e. level r+g+1) by building the one-edge graph on units at that level, deleting precise nodes,
and checking c7->c4 connectivity. We pick the entry c7 = a class-7 unit reachable from start by one
zero-edge; for the connectivity question ANY class-7 entry suffices (orbit is vertex-transitive-ish).
"""
def tau_a(a): return {1:2,2:1,4:2,5:3,7:4,8:1}[a]
X=[1,2,4,5,7,8]
from collections import deque

def oneedge_connect_avoiding_precise(L, r, j, entry, target):
    """One-edge graph at level L on units; delete precise (c==1 mod 3^(r+j)); BFS entry->target."""
    M=3**L; inv2=(M+1)//2
    precise_mod=3**(r+j)
    def precise(c): return c % precise_mod == 1
    if precise(entry) or precise(target):
        return None, "entry/target precise"
    seen={entry}; dq=deque([entry])
    while dq:
        c=dq.popleft()
        if c==target: return True, "reached"
        for a in X:
            cp=(pow(inv2,tau_a(a),M)*c)%M
            if cp%9==a and not precise(cp) and cp not in seen:
                seen.add(cp); dq.append(cp)
    return (target in seen), ("reached" if target in seen else "BLOCKED by precise")

print("=== one-edge reachability c7 -> c4 AVOIDING m-precise, at fixed j=1 ===", flush=True)
print("    (faithful r>g; precise level = r+1, working level = r+g+1)", flush=True)
for r,g in [(3,2),(4,2),(4,3),(5,3),(5,4),(6,4),(6,5),(7,5)]:
    L=r+g+1; j=1
    # find a class-7 unit and class-4 unit at this level
    entry=7; target=4  # representatives; both units
    ok,msg=oneedge_connect_avoiding_precise(L,r,j,entry,target)
    # also: how many precise vertices are in the orbit (the obstacle size)
    M=3**L; pm=3**(r+j); n_prec=len([c for c in range(M) if c%3!=0 and c%pm==1])
    print(f"  r={r} g={g} L={L}: c=7 ->(one-edges, avoid precise)-> c=4 : {ok} ({msg}); #precise-in-level={n_prec}", flush=True)

print("""
If 'True (reached)' across faithful cases: within a fixed-j level, the trap c=4 is reachable from
the class-7 entry by one-edges WITHOUT touching an m-precise vertex. Combined with the precise-free
prefix start->c7 (one zero-edge, both non-precise), the FULL path start ->...-> c=4 avoids m-precise
vertices. Then the deep one-edge c=4 -> c'=1 hits the goal (= first m-precise vertex). Suffix empty.
""")
