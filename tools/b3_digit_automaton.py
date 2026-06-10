"""
Angle B3 -- the dlog-DIGIT automaton.

DISCOVERY (b3_invariant_hunt): the affine zero-edge jump J = dlog(3c+1)-dlog(c)
mod 6 is a FUNCTION of c mod 9 only.  Test whether this 'determinacy' persists at
higher 3-adic digits:  is J mod (2*3^t) a function of c mod 3^(t+1)?

If YES at every level, then dlog evolves by a DETERMINISTIC rule on each 3-adic
digit, and we can build a finite automaton on dlog mod 2*3^t to DECIDE whether the
trap value dlog=2 is reachable and whether dlog=0 is an unavoidable predecessor.

Transition rules on the dlog value d (at level k=R+j), with c = 2^d mod 3^k:
 * one-edge: pick admissible alpha in X; new d' = d - tau(alpha) (mod ord_k); valid
   iff 2^(d' mod 6) mod 9 == alpha.  [EXACT, dlog-only]
 * zero-edge (j->j+1, level k->k+1): intermediate dlog of (3c+1) at level k+1 is
   d + J(c, k)  where J depends on c (we test: on c mod 3^(t+1)); then new
   d' = (d + J) - tau(alpha) (mod ord_{k+1}); valid iff 2^(d' mod 6) mod9==alpha.

We here VERIFY the determinacy claim at several digit levels, then build the
mod-(2*3^t) automaton and run reachability of d==2 (clean, i.e. before d==0).
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from fast_dlog import fast_dlog
from b3_trap_setup import TAU, X, aS202

def dlogv(c,k): return fast_dlog(c%3**k,k)

def test_determinacy(t, kmax=None):
    """Is J(c,j) mod 2*3^t a function of c mod 3^(t+1)?  Scan c at level k=j+1
    >= t+2 to have enough precision.  Return dict c_mod_3^(t+1) -> set(J mod 2*3^t)."""
    N = 2*3**t
    src_mod = 3**(t+1)
    buckets={}
    if kmax is None: kmax=t+4
    for k in range(t+2, kmax+1):
        M=3**k
        # enumerate c coprime to 3 fully if small else sample
        if M<=200000:
            it=(c for c in range(1,M) if c%3!=0)
        else:
            import random
            it=(random.randrange(1,M) for _ in range(20000))
        for c in it:
            if c%3==0: continue
            J=(dlogv(3*c+1,k)-dlogv(c,k))%N
            buckets.setdefault(c%src_mod,set()).add(J)
    maxsize=max(len(v) for v in buckets.values())
    return buckets, maxsize, N, src_mod

if __name__=="__main__":
    print("=== determinacy of affine jump J mod 2*3^t as function of c mod 3^(t+1) ===")
    for t in range(1,6):
        b,maxsz,N,sm=test_determinacy(t, kmax=t+4)
        print(f" t={t}: N=2*3^{t}={N}, src=c mod 3^{t+1}={sm} -> max bucket size = {maxsz} "
              f"({'DETERMINISTIC' if maxsz==1 else 'NOT deterministic'})")
        if maxsz>1:
            # show a violating bucket
            for kk,v in b.items():
                if len(v)>1:
                    print(f"    e.g. c%{sm}={kk}: J%{N} in {sorted(v)[:8]}{'...' if len(v)>8 else ''}")
                    break
