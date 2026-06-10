"""
Angle B3 -- the dlog-accounting + zero-edge-bridge analysis.

GOAL: decide whether the trap T = { v : v.c == 4 (mod 3^(R+v.j)) } (dlog=2 at
full precision) is reachable from InvStart(m) along an admissible inverse path,
WITHOUT first passing a coarse-m-precise vertex
   (a vertex w with  w.c == 1 (mod 3^(22(m-1)+2 + w.j)) ).

We work the dlog cocycle at the *fixed working modulus* 3^(R+j*) where j* is the
trap vertex's level, and study the two obstructions B3 raises:
  (P) PARITY (sign / Teichmuller bit):  dlog mod 2 = [c == 2 mod 3].
  (D) DEEP value: reach dlog == 2 exactly (not just == 2 mod something) while
      avoiding dlog == 0 at the COARSE m-level earlier.

This file derives the per-edge dlog transition law in BOTH the same-modulus
(one-edge) and the modulus-lift (zero-edge) settings, and isolates whether a
parity / value conflict forbids the trap.
"""

import sys
sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from b3_trap_setup import TAU, X, tau, order2, dlog, aS202

# ---------------------------------------------------------------------------
# PART 1.  The sign (parity) cocycle.  dlog(c) mod 2 = [c == 2 (mod 3)].
#   one-edge: c_src == 2^tau * c_tgt  => sign(src) = (tau + sign(tgt)) mod 2.
#   zero-edge: 3*c_src+1 == 2^tau * c_tgt.  LHS == 1 (mod 3) always (3c+1==1).
#             so sign of (3c+1) = 0, giving 0 = (tau + sign(tgt)) mod 2,
#             i.e. sign(tgt) = tau mod 2  (INDEPENDENT of src sign!).
# Trap has c==4 => c mod 3 = 1 => sign(trap)=0 (EVEN dlog). Goal c==1 => sign 0.
# aS202 == 1 mod 3 => sign(start) = 0.
# ---------------------------------------------------------------------------

def sign_of(c):  # dlog parity = [c==2 mod 3]
    return 1 if c % 3 == 2 else 0

def tau_parity_table():
    print("=== PART 1: sign/parity cocycle ===")
    print(" alpha  tau  tau%2")
    for a in sorted(X):
        print(f"   {a}    {TAU[a]}    {TAU[a]%2}")
    # The crucial point for the zero-edge bridge:
    # crossing a zero-edge FORCES sign(target) = tau(target) mod 2, regardless
    # of the source. So the parity of the target's dlog is pinned by its own
    # mod-9 class:
    print(" zero-edge: sign(target.c) MUST equal tau(target.c)%2:")
    for a in sorted(X):
        # is a self-consistent? target c%9=a has sign_of determined by a%3.
        s_required = TAU[a] % 2
        s_actual_from_class = 1 if a % 3 == 2 else 0
        ok = (s_required == s_actual_from_class)
        print(f"   alpha={a}: need sign={s_required}, class gives sign={s_actual_from_class}  -> {'consistent' if ok else 'IMPOSSIBLE as zero-target'}")

# ---------------------------------------------------------------------------
# PART 2.  Build the ACTUAL forward reachable graph at modulus 3^(R+j) and
#  track, per reachable vertex:  (j, c mod 3^(R+j)), full dlog, coarse-precise?
#  We enumerate outgoing edges exactly as the Lean `outgoingEdges`.
# ---------------------------------------------------------------------------

def outgoing(R, Q, j, c):
    """Yield (j', c', omega, kind) for inverse edges from (j,c).
    one-edges: c' = inv(2^tau) * c (mod 3^(R+j)) for each alpha with c'%9==alpha.
    zero-edges (if j<Q): c' = inv(2^tau) * (3c+1) (mod 3^(R+j+1))."""
    out = []
    M = 3**(R+j)
    for a in sorted(X):
        t = TAU[a]
        inv2t = pow(pow(2, t, M), -1, M)
        cp = (inv2t * c) % M
        if cp % 9 == a:
            out.append((j, cp, t, 'one'))
    if j < Q:
        Mp = 3**(R+j+1)
        for a in sorted(X):
            t = TAU[a]
            inv2t = pow(pow(2, t, Mp), -1, Mp)
            cp = (inv2t * ((3*c+1) % Mp)) % Mp
            if cp % 9 == a:
                out.append((j+1, cp, t-2, 'zero'))
    return out

def is_goal(R, j, c):
    M = 3**(R+j)
    return c % M == 1 % M

def is_trap(R, j, c):
    M = 3**(R+j)
    return c % M == 4 % M

def is_coarse_m_precise(m, j, c):
    """coarse m-precise: projection to m-level is an m-goal, i.e.
       c == 1 (mod 3^(22*(m-1)+2 + j))?  NO -- projMPrecise m at the (m+1)-cylinder.
    Careful: in FirstMPrecisionSuffixPositive the cylinder is (m+1), R=22(m+1)+2,
    and the split predicate is projMPrecise m: c == 1 (mod 3^(22m+2 + j)).
    So for a working cylinder index M_c := m (so R=22m+2), the 'coarse' precise
    level is 22*(m-1)+2 + j.  We parametrize by the WORKING m (R=22m+2) and the
    coarse level Rcoarse = 22*(m-1)+2."""
    Rcoarse = 22*(m-1) + 2
    Mc = 3**(Rcoarse + j)
    return c % Mc == 1 % Mc

def forward_search(m, Q, max_states=300000, stop_on_trap=True):
    """BFS from InvStart(m). Track whether each path has hit a coarse-m-precise
    vertex BEFORE reaching the trap. Returns dict of findings."""
    R = 22*m + 2
    start_c = aS202() % 3**R
    # state: (j, c). We also carry a flag 'passed_coarse' along the path.
    # To answer 'reachable WITHOUT first passing coarse', we do a search over
    # the product automaton (vertex, passed_coarse_flag) and ask if trap is
    # reachable with flag=False.
    from collections import deque
    start_flag = is_coarse_m_precise(m, 0, start_c)
    seen = set()
    dq = deque()
    s0 = (0, start_c, start_flag)
    dq.append(s0); seen.add((0, start_c, start_flag))
    found_trap_clean = None    # trap reached with passed_coarse == False
    found_trap_dirty = None    # trap reached but only after coarse
    trap_clean_count = 0
    coarse_seen = 0
    n = 0
    while dq and n < max_states:
        j, c, flag = dq.popleft()
        n += 1
        # check trap
        if is_trap(R, j, c):
            if not flag:
                if found_trap_clean is None:
                    found_trap_clean = (j, c)
                trap_clean_count += 1
                if stop_on_trap:
                    return dict(states=n, found_trap_clean=found_trap_clean,
                               trap_clean_count=trap_clean_count, coarse_seen=coarse_seen,
                               exhausted=False)
            else:
                if found_trap_dirty is None:
                    found_trap_dirty = (j, c)
        for (j2, c2, om, kind) in outgoing(R, Q, j, c):
            newflag = flag or is_coarse_m_precise(m, j2, c2)
            if newflag and not flag:
                coarse_seen += 1
            key = (j2, c2, newflag)
            if key not in seen:
                seen.add(key)
                dq.append((j2, c2, newflag))
    return dict(states=n, found_trap_clean=found_trap_clean,
               trap_clean_count=trap_clean_count, coarse_seen=coarse_seen,
               found_trap_dirty=found_trap_dirty, exhausted=(len(dq)==0))

if __name__ == "__main__":
    tau_parity_table()
    print()
    print("=== PART 2: forward constrained search ===")
    print(" (working cylinder index mw = residual_m + 1; coarse level = 22*(mw-1)+2)")
    # residual m=1 -> working mw=2 (R_work=46), the genuine entry point.
    for mw in [2]:
        print(f"--- working cylinder mw={mw} (R_work={22*mw+2}), residual m={mw-1} ---")
        for Q in [0,1,2,3,4,6,8,10]:
            res = forward_search(mw, Q, max_states=200000)
            print(f" Q={Q}: states={res['states']} exhausted={res['exhausted']} "
                  f"trap_clean={res['found_trap_clean']} dirty={res.get('found_trap_dirty')} "
                  f"coarse_entries={res['coarse_seen']}")
