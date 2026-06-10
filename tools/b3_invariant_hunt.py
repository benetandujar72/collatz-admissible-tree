"""
Angle B3 -- systematic hunt for a modular dlog-invariant that separates the trap.

We look for a function  Inv(j, c) = (dlog at level R+j) reduced mod some modulus N,
combined with j, that is INVARIANT (or evolves in a constrained way) along every
admissible edge, and that distinguishes:
    start:  dlog = d0
    trap :  dlog = 2
    goal :  dlog = 0

We compute, EXHAUSTIVELY over admissible edges sampled at modest level, the per-edge
change Delta = dlog(target_full) - dlog(source_full) reduced mod N, for N = 2,3,6,9,18,27.
If Delta lands in a strict subgroup/coset for ALL edges of a given type, that is an
invariant.  We already know (PROVEN cocycle): one-edge Delta == -tau exactly; zero-edge
Delta involves the affine jump.  The open part is the zero-edge.  So we focus on the
zero-edge affine jump  J(c,j) = dlog_{j+1}(3c+1) - dlog_{j+1}(c)  mod N, scanning c over
admissible residues, to see if J is constrained mod small N.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202

def dlogv(c,k): return fast_dlog(c%3**k,k)

def affine_jump(c, j):
    """J = dlog_{j+1}(3c+1) - dlog_{j+1}(c)."""
    k=j+1
    return (dlogv(3*c+1,k) - dlogv(c,k))

def scan_affine_jump_mod(N, kmax=8, samples_per_k=400):
    """Scan the affine jump J(c,j) mod N over admissible c (coprime to 3) for
    j+1=k up to kmax.  Report the SET of residues J mod N takes."""
    import random
    res_by_k={}
    for k in range(2, kmax+1):
        M=3**k
        s=set()
        seen_c=0
        # scan all c coprime to 3 if small, else sample
        if M <= 60000:
            iterc = (c for c in range(1,M) if c%3!=0)
        else:
            iterc = (random.randrange(1,M)|1 for _ in range(samples_per_k))  # odd-ish; ensure coprime below
        for c in iterc:
            if c%3==0: continue
            J = affine_jump(c, k-1) % N
            s.add(J); seen_c+=1
        res_by_k[k]=(sorted(s), seen_c)
    return res_by_k

def scan_affine_jump_by_class(N, kmax=8):
    """Refine: the jump J mod N, bucketed by source class c mod 9 (and c mod 27).
    Looking for: J mod N determined by c mod (small)."""
    buckets={}  # (cmod9) -> set of J mod N
    buckets27={}
    import random
    for k in range(3, kmax+1):
        M=3**k
        iterc = range(1,M) if M<=60000 else (random.randrange(1,M) for _ in range(3000))
        for c in iterc:
            if c%3==0: continue
            J=affine_jump(c,k-1)%N
            buckets.setdefault(c%9,set()).add(J)
            buckets27.setdefault(c%27,set()).add(J)
    return buckets, buckets27

if __name__=="__main__":
    print("=== affine zero-edge jump J = dlog(3c+1)-dlog(c) mod N ===")
    for N in [2,3,6,9,18,27,54]:
        r=scan_affine_jump_mod(N,kmax=9)
        # union across k
        allres=set()
        for k,(s,n) in r.items(): allres|=set(s)
        print(f" N={N}: J mod N takes values {sorted(allres)}  (full set Z/N? {len(allres)==N})")
    print()
    print("=== J mod 6 bucketed by source class c mod 9 ===")
    b9,b27 = scan_affine_jump_by_class(6,kmax=9)
    for c9 in sorted(b9): print(f"  c%9={c9}: J%6 in {sorted(b9[c9])}")
    print("=== J mod 6 bucketed by source class c mod 27 ===")
    for c27 in sorted(b27): print(f"  c%27={c27}: J%6 in {sorted(b27[c27])}")
    print()
    print("=== sanity: parity of J ===  (expect J even always: dlog(3c+1) even, dlog(c) parity=[c==2 mod3])")
    b2,_=scan_affine_jump_by_class(2,kmax=9)
    for c9 in sorted(b2): print(f"  c%9={c9}: J%2 in {sorted(b2[c9])}  (c mod3={c9%3})")
