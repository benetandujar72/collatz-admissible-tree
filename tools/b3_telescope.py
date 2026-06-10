"""
Angle B3 -- the dlog telescope at FIXED working precision, and the search for a
CONSERVED invariant separating aS202 (dlog=d0) from the trap (dlog=2) under the
no-coarse-precise constraint.

The cocycle (DlogReachable.lean, PROVEN):
  one-edge v->v' (same j):  dlog_K(v.c) == tau + dlog_K(v'.c)  (mod ord_K)
  zero-edge v->v' (j->j+1): dlog_{K'}(3v.c+1) == tau + dlog_{K'}(v'.c) (mod ord_{K'})
where K = R+j is the level's modulus exponent, ord_K = 2*3^(K-1).

But to compare TWO vertices at DIFFERENT j we must fix a common modulus.  The
ENTIRE path lives inside the inverse cover of the (m+1)-cylinder, i.e. modulus
3^(R+j) GROWS with j.  The trap is read at the working full precision 3^(R+jT).

Strategy: pick the deepest level jmax reached, fix Kfix = R + jmax, and PUSH every
vertex's c up to that modulus is IMPOSSIBLE (c only determined mod 3^(R+j) <= Kfix).
So instead we track dlog at EACH vertex's own level, and use dlog_reduce (PROVEN):
  dlog_j(c) == dlog_{j+1}(c) (mod ord_j)   [the tower-compatibility]
to relate levels.  The honest content: along the path, the LOW-ORDER part of dlog
(mod ord_R = 2*3^(R-1)) telescopes by Sum(tau) IF no affine x->3x+1 reindex occurred,
but every zero-edge DOES a 3x+1.  The affine jump is the open object.

Here we numerically pin: is there ANY additive/multiplicative invariant mod small
powers that the trap violates but aS202 + admissible edges preserve?  We test the
dlog value mod 3^t for small t, restricted to the j=0 fibre and across zero-edges.
"""
import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from b3_trap_setup import TAU, X, tau, order2, dlog, aS202
from b3_dlog_accounting import outgoing, is_goal, is_trap, is_coarse_m_precise

# ---------------------------------------------------------------------------
# Track dlog at the COARSE m-level (Kc = 22*(mw-1)+2 + j) for each reachable
# vertex.  KEY: the trap c==4 at working precision PROJECTS to c==4 mod coarse
# too (4 < 3^coarse), so projected-trap dlog_coarse = 2 as well.  Coarse-precise
# means dlog_coarse == 0.  We ask: along the path, what dlog_coarse values occur,
# and is dlog_coarse==2 reachable without dlog_coarse==0 occurring first?
#
# This is the CLEAN reformulation: work entirely at the coarse m-level modulus.
# Because both 'reach trap (dlog_coarse=2)' and 'avoid coarse-precise
# (dlog_coarse=0)' are statements about dlog_coarse, we can decide the conflict
# on the projected (coarse) graph -- which is the SAME inverse graph one level
# down, i.e. the m-cylinder inverse graph!
# ---------------------------------------------------------------------------

def coarse_dlog(mw, j, c):
    Kc = 22*(mw-1) + 2 + j
    return dlog(c % 3**Kc, Kc)

def project_to_coarse(mw, j, c):
    Kc = 22*(mw-1) + 2 + j
    return c % 3**Kc

def forward_coarse_track(mw, Q, max_states=200000):
    """BFS at working level mw, but record the sequence of coarse-level dlog
    values, and whether the trap's coarse projection (dlog_coarse==2) is reached
    strictly before any coarse-precise (dlog_coarse==0) vertex on the SAME path.
    Product automaton over (j, c_work, hit_coarse0)."""
    from collections import deque
    R = 22*mw + 2
    start_c = aS202() % 3**R
    s0 = (0, start_c)
    # flag = have we hit dlog_coarse==0 (coarse-precise) yet on this path
    start_flag = (coarse_dlog(mw,0,start_c) == 0)
    seen = set([(0,start_c,start_flag)])
    dq = deque([(0,start_c,start_flag)])
    n=0
    trap_clean=None; trap_dirty=None; coarse0_count=0
    cd_values_seen = set()
    while dq and n<max_states:
        j,c,flag = dq.popleft(); n+=1
        cdv = coarse_dlog(mw,j,c)
        cd_values_seen.add(cdv)
        if cdv == 2:  # coarse projection IS the trap
            if not flag and trap_clean is None:
                trap_clean=(j,c,cdv)
            elif flag and trap_dirty is None:
                trap_dirty=(j,c,cdv)
        for (j2,c2,om,kind) in outgoing(R,Q,j,c):
            f2 = flag or (coarse_dlog(mw,j2,c2)==0)
            if f2 and not flag: coarse0_count+=1
            key=(j2,c2,f2)
            if key not in seen:
                seen.add(key); dq.append((j2,c2,f2))
    return dict(states=n, trap_clean=trap_clean, trap_dirty=trap_dirty,
                coarse0_count=coarse0_count, cd_values=sorted(cd_values_seen)[:40],
                exhausted=(len(dq)==0))

if __name__ == "__main__":
    print("=== coarse-level dlog tracking (working mw=2, residual m=1) ===")
    mw=2
    d0_work = dlog(aS202()%3**(22*mw+2), 22*mw+2)
    d0_coarse = coarse_dlog(mw,0, aS202()%3**(22*mw+2))
    print(f" d0 (work k={22*mw+2}) = {d0_work}")
    print(f" d0_coarse (k={22*(mw-1)+2}) = {d0_coarse}   parity={d0_coarse%2}")
    print(f" trap dlog_coarse target = 2 ; coarse-precise = 0")
    for Q in [1,2,3,4,6,8]:
        r = forward_coarse_track(mw,Q,max_states=150000)
        print(f" Q={Q}: states={r['states']} exh={r['exhausted']} "
              f"trap_clean={r['trap_clean']} trap_dirty={r['trap_dirty']} "
              f"coarse0_hits={r['coarse0_count']}")
        print(f"      coarse-dlog values seen (sample): {r['cd_values']}")
