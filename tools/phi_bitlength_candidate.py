"""
phi_bitlength_candidate.py — S241: the ARCHIMEDEAN bit-length potential candidate.

CANDIDATE (closed form, integer-valued, NON-inductive, uniform in m):

    Phi(v) := floor((bitlen(c_v) - 1) / 4) + v.j - Q
    (c_v = canonical representative in [0, 3^(R+j)),  bitlen = Nat.size/bit-length)

PENCIL PROOF of the edge inequalities (UNCONDITIONAL — no slice restriction needed):
  one-edge  v=(j,c) -> v'=(j,y), kappa=+1,  c = (2^tau * y) mod 3^(R+j) <= 2^tau*y
     => bitlen(c) <= bitlen(y) + tau <= bitlen(y) + 4
     => floor((blc-1)/4) <= floor((bly-1)/4) + 1  => Phi(v) <= 1 + Phi(v').
  zero-edge v=(j,c) -> v'=(j+1,y):  3c+1 = (2^tau * y) mod 3^(R+j+1) <= 2^tau*y
     => y >= (3c+1)/2^tau.
     tau=1 (kappa=-1): y >= (3c+1)/2 >= 1.5c  => bitlen(y) >= bitlen(c)
        => floor-term non-decreasing, j-term +1  => Phi(v') >= Phi(v) + 1. OK
     tau=2,3,4 (kappa=0): y >= (3c+1)/2^tau > c/2^(tau-1)
        => bitlen(y) >= bitlen(c) - (tau-1) >= bitlen(c) - 3
        => floor-term drops <= 1, j-term +1  => Phi(v') >= Phi(v). OK
  goal: c=1, bitlen=1, floor(0/4)=0 => Phi(goal) = j_goal - Q <= 0 for goals in slice.
  start: Phi(InvStart m) = floor((B0(m)-1)/4) - Q,  B0(m) = bitlen(aS202 mod 3^(22m+2)).

  => S202_kappa_precise_barrier_bounded m Q  whenever floor((B0(m)-1)/4) - Q >= m.
  B0(m) ~ log2(3)*(22m+2) ~ 34.87m + 3.2  =>  valid for  Q <~ 7.7m  (NOT all Q).

This file:
  1. computes B0(m) exactly for m=1..8 and the implied (m, Q_max);
  2. smoke-tests the inequality on EVERY edge of the explored graphs (fwd table +
     backward cone) for m=1, Q in {3,5};
  3. FALSIFICATION: the candidate implies min kappa-cost(start->goal) >=
     floor((B0-1)/4) - Q + ... actually >= Phi(start) - max_goal Phi = floor((B0-1)/4) - Q.
     Run the exact engine threshold scan ABOVE the previously certified T to check the
     prediction (a witness below the bound would refute the pencil proof).
"""
from __future__ import annotations
import sys, time
from collections import deque

sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from kappa_precise_probe import KappaEngine
from s202_engine import State, a202_mod


def phi(v_j, v_c, Q):
    return (v_c.bit_length() - 1) // 4 + v_j - Q


def part1():
    print("=== 1. B0(m) and the implied uniform bound ===")
    for m in range(1, 9):
        R = 22 * m + 2
        B0 = a202_mod(R).bit_length()
        qmax = (B0 - 1) // 4 - m
        print(f"  m={m}: R={R}  B0=bitlen(aS202 mod 3^R)={B0}  "
              f"floor((B0-1)/4)={(B0-1)//4}  => barrier(m,Q) for Q <= {qmax}")


def part2(m, Q, T_hi=5, max_states=400_000):
    print(f"=== 2. edge smoke-test m={m} Q={Q} (fwd table + backward cone) ===")
    for T in range(T_hi, 0, -1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        res = eng.search_or_certify_bf(max_states=max_states)
        if res["status"] == "barrier_certificate":
            break
    R = eng.R
    viol = 0
    checked = 0
    worst = None
    for s in res["states"]:
        j, c = s["j"], s["c"]
        pv = phi(j, c, Q)
        for (tgt, w) in eng.outgoing_edges(State(j, c)):
            checked += 1
            slack = w + phi(tgt.j, tgt.c, Q) - pv
            if slack < 0:
                viol += 1
                worst = (j, c, tgt.j, tgt.c, w, slack)
    # backward cone edges too
    from s202_engine import TAU
    bw_checked = 0
    seen = set()
    qq = deque((jj, 1) for jj in range(Q + 1))
    seen.update(qq)
    depth = {x: 0 for x in qq}
    while qq:
        (j, c) = qq.popleft()
        if depth[(j, c)] >= 14:
            continue
        M = 3 ** (R + j)
        t = TAU[c % 9]
        preds = [((j, (pow(2, t, M) * c) % M), 1)]
        if j >= 1:
            v = (pow(2, t, M) * c) % M
            preds.append(((j - 1, (v - 1) // 3), -1 if t == 1 else 0))
        for (p, w) in preds:
            bw_checked += 1
            slack = w + phi(j, c, Q) - phi(p[0], p[1], Q)
            if slack < 0:
                viol += 1
                worst = (p[0], p[1], j, c, w, slack)
            if p not in seen and len(seen) < 60_000:
                seen.add(p)
                depth[p] = depth[(j, c)] + 1
                qq.append(p)
    print(f"  forward edges checked: {checked}, backward-cone edges: {bw_checked}, "
          f"VIOLATIONS: {viol}" + (f"  worst={worst}" if worst else ""))
    # endpoint constraints
    start_phi = phi(0, a202_mod(R), Q)
    print(f"  Phi(start) = {start_phi}  (need >= m={m}: {'OK' if start_phi >= m else 'FAIL'})")
    print(f"  Phi(goal at j) = j - Q <= 0 for all j <= Q: OK by construction")


def part3(m, Q, T_max):
    print(f"=== 3. FALSIFICATION scan m={m} Q={Q}: engine thresholds up to T={T_max} ===")
    R = 22 * m + 2
    bound = (a202_mod(R).bit_length() - 1) // 4 - Q
    print(f"  candidate-implied bound: min kappa(start->goal,j<=Q) >= "
          f"Phi(start) - 0 = {bound}")
    for T in range(1, T_max + 1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        t0 = time.time()
        res = eng.search_or_certify_bf(max_states=1_500_000)
        st = res["status"]
        extra = ""
        if st == "useful_path":
            extra = f"witness cost={res['dist']} at {res['state']}"
            ok = res["dist"] >= bound
            extra += f"  -> witness {'consistent (>= bound)' if ok else 'REFUTES CANDIDATE'}"
        elif st == "barrier_certificate":
            extra = f"states={res['states_seen']} (min >= {T})"
        else:
            extra = f"INCOMPLETE at {res.get('states_seen')} states"
        print(f"  T={T}: {st:<22} {extra}  [{time.time()-t0:.0f}s]", flush=True)
        if st == "useful_path":
            break
        if st == "incomplete":
            break


if __name__ == "__main__":
    part1()
    print()
    for Q in (3, 5):
        part2(1, Q)
        print()
    # falsification: bounds are 9-Q; scan to bound+1 to find the exact min or confirm
    for Q in (1, 2, 3, 5):
        R = 24
        bound = (a202_mod(R).bit_length() - 1) // 4 - Q
        part3(1, Q, T_max=bound + 1)
        print()
