"""
phi_hybrid_gate.py — GATE H (S243): the HYBRID potential class, decided by LP with
constraint generation (no region enumeration => reaches the Q ~ 22m wall).

THE CLASS BEING TESTED.  PhiBitlen (BitlenPotential.lean) is linear in the
archimedean features (bitlen(c), j) and proves the bounded kappa-barrier up to the
bit criterion 4(m+Q)+1 <= size(start) — for the 73-bit faithful start, Q <= 17 at
m=1.  The S242 no-go kills every 3-adically-CONTINUOUS real corrector, and the
realkam interior profile already constrains "Green poles + Hoelder remainder".
But the TRUE hybrid suggested by the attractor identities is NOT covered by any
proven no-go:

    Phi(j, c) = th_1 + th_j*j + th_bl*bitlen(c) + th_p1*nu3(c-1) + th_pm1*nu3(c+1)

— archimedean part (NOT 3-adically continuous) PLUS singular poles at the two
attractors c=1 (tau=2 chain, identity 4(y-1)=3(c-1): nu3(c-1) is the EXACT chain
clock) and c=-1 (tau=1 filament, identity 2(y+1)=3(c+1)).  The start itself sits
on the deep +1 shell: nu3(aS202 - 1) = 22.

THE CONTRACT (S202_kappa_precise_barrier_bounded_from_potential, universal form):
    (E)  Phi(u) <= kappa(e) + Phi(v)   for every edge u -> v with j <= Q
    (G)  Phi((j,1)) <= 0               for every goal level j <= Q
    (S)  Phi(start) >= m
Any Phi of the class satisfying (E)+(G)+(S) proves the barrier at (m, Q).

METHOD.  The slice at Q ~ 22 has ~10^8+ states: full enumeration is impossible.
But the LP has only d=5 unknowns, so CONSTRAINT GENERATION decides it:
  * working set W of TRUE rows (each row re-derivable from raw edge arithmetic);
  * LP: minimize s  s.t.  a_i . theta - s <= b_i  (s >= 0);
  * s* > 0  =>  INFEASIBLE: extract the Farkas combination (support <= d+1 rows),
    re-derive it EXACTLY over the rationals (Fraction Gaussian elimination) and
    re-verify every support row against the engine by an independent code path.
    A verified certificate is a RIGOROUS death of the class at (m, Q): finitely
    many true constraints already contradict (S)+(G).
  * s* = 0  =>  candidate theta*; the SEPARATION ORACLE hunts violated true rows:
      - the +1 attractor chain (zero-edges maximizing nu3(c'-1)) from many seeds,
      - the -1 filament (tau=1 zero-edges, kappa=-1) from many seeds,
      - greedy violation walks under theta*,
      - capped low-kappa Dijkstra bursts (real min-kappa structure + goals),
      - random admissible walks.
    No violation found under budget => "SURVIVOR at (m,Q)" (epistemically: not
    refuted at this oracle budget — the standard gate convention).  SURVIVOR is
    NOT a feasibility proof: the S245 audit showed the walk-based oracle alone
    missed in-slice edges (notably the goal-adjacent trap edge (j,4)->(j,1))
    that kill the pole-enriched class at the SAME step as the linear class;
    `add_universal_rows` now seeds those families explicitly.  Genuine
    feasibility at (1,7)/(2,16) follows from the linear PhiBitlen relaxation
    theta = (c0, 1, 1/4, 0, 0), valid by the Lean size lemmas.
CONTROL: the restricted class th_p1 = th_pm1 = 0 (the (bitlen, j)-linear class)
must die by Q ~ 18-24; if the oracle cannot kill it there, the oracle is too
weak to trust a full-class survival.

Usage:  python phi_hybrid_gate.py [Q ...]     (default sweep: 5 10 14 18 22 26)
"""
from __future__ import annotations
import sys, json, time, random
from fractions import Fraction
from collections import deque

sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from s202_engine import State, a202_mod
from kappa_precise_probe import KappaEngine

import numpy as np
from scipy.optimize import linprog

FEAT = ["one", "j", "bl", "p1", "pm1"]
D = len(FEAT)
INF = float("inf")


def nu3_res(x: int, depth: int) -> int:
    """3-adic valuation of the residue x in [0, 3^depth), with nu3(0) := depth."""
    if x == 0:
        return depth
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v


def phi(eng, s: State):
    depth = eng.R + s.j
    M = eng.modulus(s.j)
    c = s.c % M
    return (1, s.j, c.bit_length(),
            nu3_res((c - 1) % M, depth), nu3_res((c + 1) % M, depth))


# --------------------------------------------------------------------------
class RowSet:
    """Deduplicated true rows  a . theta <= b,  each with a concrete witness."""

    def __init__(self, eng, m):
        self.eng, self.m = eng, m
        self.rows = []          # (a: tuple[int], b: int, witness)
        self.seen = set()       # row-content dedup
        self.edge_seen = set()  # (uj,uc,vj,vc) edges already converted

    def _push(self, a, b, wit):
        key = (a, b)
        if key in self.seen:
            return False
        self.seen.add(key)
        self.rows.append((a, b, wit))
        return True

    def add_edge(self, u: State, v: State, w: int) -> bool:
        ek = (u.j, u.c, v.j, v.c)
        if ek in self.edge_seen:
            return False
        self.edge_seen.add(ek)
        pu, pv = phi(self.eng, u), phi(self.eng, v)
        a = tuple(x - y for x, y in zip(pu, pv))
        return self._push(a, w, ("E", u.j, u.c, v.j, v.c, w))

    def add_goal(self, j: int) -> bool:
        g = State(j, 1)
        return self._push(phi(self.eng, g), 0, ("G", j))

    def add_start(self) -> bool:
        st = self.eng.start
        a = tuple(-x for x in phi(self.eng, st))
        return self._push(a, -self.m, ("S", st.j, st.c))


# --------------------------------------------------------------------------
def cols_of(restrict: bool):
    """Active feature columns: restricted mode DROPS the pole columns entirely
    (projection, not bounds — keeps Farkas certificates clean)."""
    return [0, 1, 2] if restrict else list(range(D))


def solve_lp(rows, restrict: bool):
    """min s  s.t.  a.theta - s <= b  on the active columns.
    Returns (s*, theta* embedded in R^D, marginals)."""
    cols = cols_of(restrict)
    d = len(cols)
    n = len(rows)
    A = np.zeros((n, d + 1))
    b = np.zeros(n)
    for i, (a, bb, _) in enumerate(rows):
        A[i, :d] = [a[c] for c in cols]
        A[i, d] = -1.0
        b[i] = bb
    bounds = [(None, None)] * d + [(0.0, None)]
    res = linprog(c=[0.0] * d + [1.0], A_ub=A, b_ub=b, bounds=bounds,
                  method="highs")
    if not res.success:
        raise RuntimeError(f"LP solver failure: {res.message}")
    theta = np.zeros(D)
    for k, c in enumerate(cols):
        theta[c] = res.x[k]
    return res.fun, theta, res.ineqlin.marginals


def robust_theta(rows, restrict: bool):
    """Among feasible thetas, maximize the uniform slack t <= 1 (better oracle bait)."""
    cols = cols_of(restrict)
    d = len(cols)
    n = len(rows)
    A = np.zeros((n, d + 1))
    b = np.zeros(n)
    for i, (a, bb, _) in enumerate(rows):
        A[i, :d] = [a[c] for c in cols]
        A[i, d] = 1.0          # a.theta + t <= b
        b[i] = bb
    bounds = [(None, None)] * d + [(None, 1.0)]
    res = linprog(c=[0.0] * d + [-1.0], A_ub=A, b_ub=b, bounds=bounds,
                  method="highs")
    if not res.success:
        return None
    theta = np.zeros(D)
    for k, c in enumerate(cols):
        theta[c] = res.x[k]
    return theta


# --------------------------------------------------------------------------
# Farkas certificate: exact rational verification
# --------------------------------------------------------------------------
def farkas_exact(rows, marginals, s_star, restrict=False):
    """y = -marginals >= 0,  sum y_i a_i = 0 (active cols),  sum y_i b_i < 0.
    Re-derive y exactly over Q on the support; verify signs and the b-sum."""
    cols = cols_of(restrict)
    dc = len(cols)
    y = np.maximum(-np.asarray(marginals), 0.0)
    tot = y.sum()
    if tot <= 0:
        return None, "empty dual"
    y /= tot
    sup = [i for i in range(len(rows)) if y[i] > 1e-12]
    if len(sup) > 24:
        sup = sorted(sup, key=lambda i: -y[i])[:24]
    # exact nullspace of the dc x k matrix of support a-vectors
    k = len(sup)
    M = [[Fraction(rows[i][0][c]) for i in sup] for c in cols]
    M.append([Fraction(1)] * k)        # normalization sum y = 1
    rhs = [Fraction(0)] * dc + [Fraction(1)]
    # Gaussian elimination on (dc+1) x k augmented system M y = rhs
    rowsM = [M[r][:] + [rhs[r]] for r in range(dc + 1)]
    piv_cols = []
    pr = 0
    for col in range(k):
        piv = next((r for r in range(pr, dc + 1) if rowsM[r][col] != 0), None)
        if piv is None:
            continue
        rowsM[pr], rowsM[piv] = rowsM[piv], rowsM[pr]
        pv = rowsM[pr][col]
        rowsM[pr] = [x / pv for x in rowsM[pr]]
        for r in range(dc + 1):
            if r != pr and rowsM[r][col] != 0:
                f = rowsM[r][col]
                rowsM[r] = [x - f * z for x, z in zip(rowsM[r], rowsM[pr])]
        piv_cols.append(col)
        pr += 1
        if pr == dc + 1:
            break
    for r in range(pr, dc + 1):          # inconsistency check
        if rowsM[r][k] != 0:
            return None, "support system inconsistent"
    free = [c for c in range(k) if c not in piv_cols]
    yex = [Fraction(0)] * k
    if free:                              # pin free vars to numeric values
        for c in free:
            yex[c] = Fraction(y[sup[c]] / sum(y[sup[cc]] for cc in range(k))
                              ).limit_denominator(10 ** 9)
    for idx, col in enumerate(piv_cols):
        val = rowsM[idx][k]
        for c in free:
            val -= rowsM[idx][c] * yex[c]
        yex[col] = val
    if any(v < 0 for v in yex):
        return None, "negative exact multiplier"
    # exact checks
    for c in cols:
        if sum(yex[t] * rows[sup[t]][0][c] for t in range(k)) != 0:
            return None, "sum y a != 0 exactly"
    bsum = sum(yex[t] * rows[sup[t]][1] for t in range(k))
    if not bsum < 0:
        return None, "sum y b not negative"
    cert = [(rows[sup[t]][2], str(yex[t])) for t in range(k) if yex[t] != 0]
    return {"support": cert, "b_combination": str(bsum)}, "ok"


def reverify_witness(eng, m, wit) -> bool:
    """Independent re-derivation of a row witness from raw arithmetic."""
    kind = wit[0]
    if kind == "S":
        _, j, c = wit
        return j == 0 and c == a202_mod(eng.R)
    if kind == "G":
        return 0 <= wit[1] <= eng.Q
    _, uj, uc, vj, vc, w = wit
    M = eng.modulus(vj)
    alpha = vc % 9
    if alpha not in (1, 2, 4, 5, 7, 8):
        return False
    t = {1: 2, 2: 1, 4: 2, 5: 3, 7: 4, 8: 1}[alpha]
    if vj == uj:                       # one-edge: 2^t * v == u, kappa = +1
        return (pow(2, t, M) * vc) % M == uc % M and w == 1
    if vj == uj + 1 and uj < eng.Q:    # zero-edge: 2^t * v == 3u+1, kappa
        ok = (pow(2, t, M) * vc) % M == (3 * uc + 1) % M
        return ok and w == (-1 if t == 1 else 0)
    return False


# --------------------------------------------------------------------------
# separation oracle
# --------------------------------------------------------------------------
class Oracle:
    def __init__(self, eng, m, Q, seed=2433):
        self.eng, self.m, self.Q = eng, m, Q
        self.rng = random.Random(seed)
        self.deep_seeds = set()          # states seen with deep p1/pm1

    def chain(self, rs: RowSet, s: State, coord: int, maxlen=None):
        """Follow zero-edges maximizing feature `coord` (3=p1, 4=pm1)."""
        n = 0
        while s.j < self.Q and (maxlen is None or n < maxlen):
            zs = [(v, w) for (v, w) in self.eng.outgoing_edges(s) if v.j == s.j + 1]
            if not zs:
                break
            best = max(zs, key=lambda vw: phi(self.eng, vw[0])[coord])
            for (v, w) in zs:
                rs.add_edge(s, v, w)
            s = best[0]
            n += 1
        return s

    def greedy_violation_walk(self, rs: RowSet, theta, maxlen):
        s = self.eng.start
        for _ in range(maxlen):
            edges = self.eng.outgoing_edges(s)
            if not edges:
                break
            scored = []
            pu = phi(self.eng, s)
            for (v, w) in edges:
                pv = phi(self.eng, v)
                vio = sum(t * (x - y) for t, x, y in zip(theta, pu, pv)) - w
                scored.append((vio, self.rng.random(), v, w))
                rs.add_edge(s, v, w)
            scored.sort(reverse=True)
            # mostly exploit, sometimes explore
            pick = scored[0] if self.rng.random() < 0.8 else \
                self.rng.choice(scored)
            s = pick[2]
            p = phi(self.eng, s)
            if p[3] >= 3 or p[4] >= 3:
                self.deep_seeds.add(s)
            if s.j >= self.Q and self.rng.random() < 0.3:
                break

    def random_walk(self, rs: RowSet, maxlen):
        s = self.eng.start
        for _ in range(maxlen):
            edges = self.eng.outgoing_edges(s)
            if not edges:
                break
            for (v, w) in edges:
                rs.add_edge(s, v, w)
            s = self.rng.choice(edges)[0]
            p = phi(self.eng, s)
            if p[3] >= 3 or p[4] >= 3:
                self.deep_seeds.add(s)

    def dijkstra_burst(self, rs: RowSet, max_states):
        """Low-kappa BFS with the optimistic cut (threshold m), capped."""
        import heapq
        eng, m, Q = self.eng, self.m, self.Q
        start = eng.start
        dist = {start: 0}
        pq = [(0, 0, start)]
        cnt = 0
        npop = 0
        while pq and len(dist) < max_states:
            d, _, s = heapq.heappop(pq)
            npop += 1
            if d > dist.get(s, INF):
                continue
            if d - (Q - s.j) >= m + 4:   # widened optimistic cut (oracle harvest)
                continue
            for (v, w) in eng.outgoing_edges(s):
                rs.add_edge(s, v, w)
                nd = d + w
                if nd < dist.get(v, INF):
                    dist[v] = nd
                    cnt += 1
                    heapq.heappush(pq, (nd, cnt, v))
                p = phi(eng, v)
                if p[3] >= 4 or p[4] >= 4:
                    self.deep_seeds.add(v)
        return len(dist)

    def burst(self, rs: RowSet, theta, round_no):
        t0 = time.time()
        n0 = len(rs.rows)
        # chains from start and from accumulated deep seeds
        self.chain(rs, self.eng.start, 3)
        self.chain(rs, self.eng.start, 4)
        seeds = list(self.deep_seeds)
        self.rng.shuffle(seeds)
        for s in seeds[:60]:
            self.chain(rs, s, 3)
            self.chain(rs, s, 4)
        if theta is not None:
            for _ in range(60):
                self.greedy_violation_walk(rs, theta, self.Q + 25)
        for _ in range(120):
            self.random_walk(rs, self.Q + 25)
        if round_no <= 2:
            self.dijkstra_burst(rs, 60_000 * round_no)
        return len(rs.rows) - n0, time.time() - t0


# --------------------------------------------------------------------------
def violated(rows, theta, tol=1e-7):
    out = []
    for i, (a, b, _) in enumerate(rows):
        v = sum(t * x for t, x in zip(theta, a)) - b
        if v > tol:
            out.append((v, i))
    return out



def add_universal_rows(eng, rs: RowSet, Q: int) -> int:
    """The contract (E) quantifies over EVERY edge of the slice j <= Q, reachable from
    the start or not.  The walk-based oracle only harvests start-reachable edges, so
    we add explicit in-slice families that the audit (S245) showed to be decisive:
      * (j,4) -> (j,1): the goal's own one-edge predecessor (tau=2, kappa=+1); the mod-9
        trap sits next to the goal and nu3(c-1) jumps 1 -> full depth on a kappa=+1 edge;
      * (j, 2*3^(R+j-1)-1) -> its zero-edges: leaving the deep -1 shell (nu3(c+1) crash);
      * (0,112) -> (0,7) (tau=4 one-edge, the theta_size <= 1/4 enforcer) and
        (0,17) -> (1,26) (tau=1 zero-edge, kappa=-1).
    All rows are true edges (checked by outgoing_edges); returns the number added."""
    R = eng.R
    added = 0
    for j in range(Q + 1):
        u = State(j, 4)
        for (tgt, w) in eng.outgoing_edges(u):
            if tgt == State(j, 1):
                added += rs.add_edge(u, tgt, w)
        if j < Q:
            u = State(j, 2 * 3 ** (R + j - 1) - 1)
            for (tgt, w) in eng.outgoing_edges(u):
                added += rs.add_edge(u, tgt, w)
    for (u, v) in [(State(0, 112), State(0, 7)), (State(0, 17), State(1, 26))]:
        for (tgt, w) in eng.outgoing_edges(u):
            if tgt == v:
                added += rs.add_edge(u, tgt, w)
    return added

def run(m, Q, restrict, max_rounds=14, budget_s=420):
    label = "RESTRICTED (bitlen,j)" if restrict else "FULL hybrid (+nu3 poles)"
    print(f"--- m={m} Q={Q}  [{label}] ---", flush=True)
    eng = KappaEngine(m=m, Q=Q, threshold=m)
    rs = RowSet(eng, m)
    rs.add_start()
    for j in range(Q + 1):
        rs.add_goal(j)
    add_universal_rows(eng, rs, Q)
    orc = Oracle(eng, m, Q)
    theta = None
    t0 = time.time()
    verdict = None
    for rnd in range(1, max_rounds + 1):
        new, dt = orc.burst(rs, theta, rnd)
        s_star, th, marg = solve_lp(rs.rows, restrict)
        if s_star > 1e-7:
            cert, msg = farkas_exact(rs.rows, marg, s_star, restrict)
            okrows = (cert is not None and
                      all(reverify_witness(eng, m, w) for w, _ in cert["support"]))
            tag = ("EXACT rational Farkas, all rows independently re-verified"
                   if cert and okrows else f"numeric only ({msg})")
            print(f"  round {rnd}: rows={len(rs.rows)} (+{new})  s*={s_star:.4g}"
                  f"  => INFEASIBLE — class DEAD at (m={m},Q={Q})  [{tag}]")
            if cert and okrows:
                for w, mult in cert["support"]:
                    print(f"      y={mult:<12} row {w}")
            verdict = {"verdict": "DEAD", "rounds": rnd, "rows": len(rs.rows),
                       "s_star": s_star, "certificate_exact": bool(cert and okrows),
                       "certificate": cert}
            break
        theta = robust_theta(rs.rows, restrict)
        if theta is None:
            theta = th
        vio = violated(rs.rows, theta)
        print(f"  round {rnd}: rows={len(rs.rows)} (+{new}, {dt:.0f}s)  s*=0 "
              f" theta=({', '.join(f'{t:.4g}' for t in theta)})"
              f"  working-set violations={len(vio)}", flush=True)
        if time.time() - t0 > budget_s:
            print(f"  time budget exhausted")
            break
    if verdict is None:
        # final hard exploration shot at theta*
        n_extra, _ = orc.burst(rs, theta, 3)
        s2, th2, marg2 = solve_lp(rs.rows, restrict)
        if s2 > 1e-7:
            cert, msg = farkas_exact(rs.rows, marg2, s2, restrict)
            okrows = (cert is not None and
                      all(reverify_witness(eng, m, w) for w, _ in cert["support"]))
            print(f"  final burst kills it: s*={s2:.4g} => DEAD "
                  f"[{'EXACT' if cert and okrows else 'numeric'}]")
            verdict = {"verdict": "DEAD", "rounds": "final", "rows": len(rs.rows),
                       "s_star": s2, "certificate_exact": bool(cert and okrows),
                       "certificate": cert}
        else:
            theta = robust_theta(rs.rows, restrict)
            if theta is None:
                theta = th2
            print(f"  => SURVIVOR at (m={m},Q={Q}): theta* = "
                  f"({', '.join(f'{t:.5g}' for t in theta)}) over {len(rs.rows)} "
                  f"true rows; no violated row found at this oracle budget")
            verdict = {"verdict": "SURVIVOR", "rows": len(rs.rows),
                       "theta": list(map(float, theta))}
    print(flush=True)
    return verdict


if __name__ == "__main__":
    args = sys.argv[1:]
    m = 1
    if args and args[0].startswith("m="):
        m = int(args[0][2:])
        args = args[1:]
    qs = [int(a) for a in args] or [5, 10, 14, 18, 22, 26]
    out = {}
    print("=== GATE H: hybrid potential LP (constraint generation) ===")
    print(f"features: {FEAT}; contract (E)+(G)+(S); m={m} sweep Q={qs}\n")
    for Q in qs:
        for restrict in (True, False):
            key = f"m{m}_Q{Q}_{'restricted' if restrict else 'full'}"
            out[key] = run(m, Q, restrict)
    path = (r"C:\Users\benet\Downloads\collatz-admissible-tree\tools"
            + f"\\phi_hybrid_gate_data_m{m}.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print(f"[data written to {path}]")
    print("\nSUMMARY")
    for k, v in out.items():
        extra = ""
        if v["verdict"] == "SURVIVOR":
            extra = "  theta=" + ", ".join(f"{t:.4g}" for t in v["theta"])
        if v["verdict"] == "DEAD":
            extra = f"  (exact cert: {v.get('certificate_exact')})"
        print(f"  {k:<18} {v['verdict']}{extra}")
