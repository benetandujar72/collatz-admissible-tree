"""
phi_realkam_lp.py — GATE A (S242): REAL-valued 3-adically-continuous corrector LP.

THE LOOPHOLE BEING TESTED. The S241 continuity collapse (discrete codomain =>
locally constant => factors through c mod 3^t => dead by Reach=units) assumed
Phi : InvVertex -> Int.  A REAL-valued Phi that is 3-adically continuous on the
unit sphere Z_3^x is NOT excluded by any proven no-go.  This gate asks, at the
scale of the verified m=1 certificates, whether such a "weak-KAM corrector"
can exist.

THE LP.  Variables Phi(v) in R for every state v=(j,c) of the certified region
(forward kappa table at the largest certifying threshold T, PLUS the backward
goal cone of phi_quotient_refuter, PLUS all real edge-targets of those states).
Constraints (exactly those of S202_kappa_precise_barrier_bounded_from_potential,
AnalyticBarrier.lean):
    (E)  Phi(v) <= kappa + Phi(v')   for every real kappa-precise edge v -> v'
    (G)  Phi(goal) <= 0              for every goal (c = 1) in the region
    (S)  Phi(start) >= m
    (C)  |Phi(u) - Phi(v)| <= L * 3^(-alpha*t),  t = nu3(c_u - c_v),
         for every pair u, v at the SAME level j           [Hoelder(L, alpha)]
Without (C) the system is feasible (the exact value function solves it).

KEY REDUCTION (what makes this exact instead of a 10^10-row LP): every
constraint above is a DIFFERENCE constraint, so the LP is feasible iff the
constraint digraph has no negative cycle.  Because real edges never decrease j
and hops never change j, the only possible negative cycles pass through the
start->goal gadget; hence

    LP(L, alpha) feasible  <=>  min over goals of SP_G*(start, goal) >= m,

where G* = region real edges + "hop" moves u ~> v (same j) of cost
L*3^(-alpha*nu3(c_u-c_v)).  Hops are encoded EXACTLY (not approximately) by an
ultrametric dendrogram gadget per level: a hub at each splitting 3-adic ball
B (scale t) with zero-cost membership chains and one turnaround edge of cost
L*3^(-alpha*t); the cheapest hub above any pair (u,v) is their deepest common
ball, scale nu3(c_u-c_v).  Dijkstra is made valid by the Johnson reweight
h = level (zero-edges have kappa >= -1 and raise j by 1, so w+1 >= 0).

EPISTEMIC STATUS of each outcome (same convention as phi_quotient_refuter):
  * INFEASIBLE at (L, alpha)  =>  RIGOROUS refutation: the witness path is a
    finite set of true constraints of the full graph that already contradict
    (S)+(G).  No Phi with that Hoelder profile exists, period.  Each witness
    is re-verified by direct arithmetic (edge laws + nu3) independent of the
    graph plumbing.
  * FEASIBLE at (L, alpha)    =>  only "no obstruction at this finite scale";
    the full graph has more states, hence more constraints.

Outputs: per (m, Q): the single-hop depth profile g(t), the empirical modulus
of continuity of the exact cost-to-goal psi, the feasibility frontier L*(alpha)
(exact multi-hop by bisection + single-hop closed form on a fine alpha grid),
the witness path at the frontier (which edges/hops break it), the f_emp-profile
verdict, and the shape (feature correlations) of a feasible Phi when one
exists.  JSON dump: tools/phi_realkam_lp_data.json.

Usage:  python phi_realkam_lp.py [Q ...]      (default: 3 5)
"""
from __future__ import annotations
import sys, json, time, math, heapq, random
from collections import defaultdict

sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from kappa_precise_probe import KappaEngine
from s202_engine import State, a202_mod, TAU
from phi_quotient_refuter import backward_region
from fast_dlog import fast_dlog

INF = float("inf")
POW3 = [3 ** i for i in range(80)]


def nu3(x: int) -> int:
    """Exact 3-adic valuation of a nonzero integer."""
    assert x != 0
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v


def best_table(m, Q, T_hi, max_states):
    for T in range(T_hi, 0, -1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        res = eng.search_or_certify_bf(max_states=max_states)
        if res["status"] == "barrier_certificate":
            return T, eng, res["states"]
    return None, None, None


# --------------------------------------------------------------------------
# Region = forward certified table + backward goal cone + 1-ring of targets
# --------------------------------------------------------------------------
class Region:
    def __init__(self, m, Q, T_hi=5, max_states=400_000, cap=6):
        self.m, self.Q = m, Q
        t0 = time.time()
        T, eng, fstates = best_table(m, Q, T_hi, max_states)
        if T is None:
            raise RuntimeError(f"no certified kappa table for m={m} Q={Q}")
        self.T, self.eng, self.R = T, eng, eng.R
        R = self.R
        psi_cone, bedges = backward_region(m, Q, R, cap=cap, max_states=600_000)
        self.psi_cone = psi_cone
        self.fdist = {(s["j"], s["c"]): s["dist"] for s in fstates}

        self.id_of: dict = {}
        self.jc_of: list = []

        def nid(j, c):
            key = (j, c)
            i = self.id_of.get(key)
            if i is None:
                i = len(self.jc_of)
                self.id_of[key] = i
                self.jc_of.append(key)
            return i

        eset = {}
        src = set(self.fdist) | set(psi_cone)
        for (j, c) in src:
            u = nid(j, c)
            for (tgt, w) in eng.outgoing_edges(State(j, c)):
                v = nid(tgt.j, tgt.c)
                k = (u, v)
                if k not in eset or w < eset[k]:
                    eset[k] = w
        for (jp, cp, j2, c2, w) in bedges:
            k = (nid(jp, cp), nid(j2, c2))
            if k not in eset or w < eset[k]:
                eset[k] = w
        self.redges = [(u, v, w) for (u, v), w in eset.items()]
        self.start = self.id_of[(0, a202_mod(R))]
        self.goals = [i for i, (j, c) in enumerate(self.jc_of) if c == 1]
        self.n_states = len(self.jc_of)
        self.level = [j for (j, c) in self.jc_of]

        # ---- ultrametric dendrogram hubs per level ----
        self.hubs = []  # {"j","t","reps":[('s',sid)|('h',hidx), ...]}
        by_level = defaultdict(list)
        for i, (j, c) in enumerate(self.jc_of):
            by_level[j].append(i)
        for j in sorted(by_level):
            ids = by_level[j]
            if len(ids) >= 2:
                self._build_dendro(ids, 0, j)
        self.n_hubs = len(self.hubs)
        self.up0 = self.n_states                       # up node of hub h: up0+2h
        self.N = self.n_states + 2 * self.n_hubs       # down node: up0+2h+1

        # structural (weight-0) edges + turnarounds (weight hop(t))
        self.struct = []           # (a, b) cost 0
        self.turns = []            # (up, down, t)  cost hop(t)
        for hidx, h in enumerate(self.hubs):
            up, down = self.up0 + 2 * hidx, self.up0 + 2 * hidx + 1
            self.turns.append((up, down, h["t"]))
            for rep in h["reps"]:
                if rep[0] == 's':
                    a = rep[1]
                    self.struct.append((a, up))
                    self.struct.append((down, a))
                else:
                    cu = self.up0 + 2 * rep[1]
                    self.struct.append((cu, up))
                    self.struct.append((down, cu + 1))
        self.hub_level = [h["j"] for h in self.hubs]
        lev = self.level + [x for h in self.hubs for x in (h["j"], h["j"])]
        self.node_level = lev

        # ---- forward / reverse adjacency with Johnson reweight ----
        # entry: (target, fixed_reweighted_cost, tscale) ; tscale = -1 fixed
        self.adjF = [[] for _ in range(self.N)]
        self.adjR = [[] for _ in range(self.N)]
        for (u, v, w) in self.redges:
            dw = self.node_level[v] - self.node_level[u]   # 0 or +1
            self.adjF[u].append((v, float(w + dw), -1))    # h = -level
            self.adjR[v].append((u, float(w + dw), -1))    # h = +level
        for (a, b) in self.struct:
            self.adjF[a].append((b, 0.0, -1))
            self.adjR[b].append((a, 0.0, -1))
        for (up, down, t) in self.turns:
            self.adjF[up].append((down, 0.0, t))
            self.adjR[down].append((up, 0.0, t))
        print(f"  region m={m} Q={Q}: R={R} T={T} | fwd table {len(self.fdist)}, "
              f"cone {len(psi_cone)}, total state-nodes {self.n_states}, "
              f"real edges {len(self.redges)}, hubs {self.n_hubs} "
              f"[{time.time()-t0:.0f}s]", flush=True)

    def _build_dendro(self, ids, t, j):
        """Recursive dendrogram of the 3-adic ultrametric on {c : (j,c) in region}."""
        while True:
            if len(ids) == 1:
                return ('s', ids[0])
            kids = defaultdict(list)
            for i in ids:
                kids[(self.jc_of[i][1] // POW3[t]) % 3].append(i)
            if len(kids) == 1:
                t += 1
                continue
            reps = [self._build_dendro(v, t + 1, j) for v in kids.values()]
            hidx = len(self.hubs)
            self.hubs.append({"j": j, "t": t, "reps": reps})
            return ('h', hidx)

    # ------------------------------------------------------------------
    def hopw(self, L, alpha, tmax=None):
        tmax = tmax if tmax is not None else self.R + self.Q + 2
        return [L * 3.0 ** (-alpha * t) for t in range(tmax + 1)]

    def dijkstra(self, forward=True, hop=None, seeds=None, want_par=False,
                 stop_label=None, use_hops=True):
        """Johnson-reweighted Dijkstra.  hop: array of turnaround costs per scale
        (None => hops disabled).  Returns (labels, parents).
        forward: seeds={start:0}; true dist(v) = label[v] - level(v).
        reverse: seeds={g: -level(g)}; true psi(v) = label[v] + level(v)."""
        adj = self.adjF if forward else self.adjR
        if seeds is None:
            seeds = ({self.start: 0.0} if forward else
                     {g: -float(self.node_level[g]) for g in self.goals})
        lab = [INF] * self.N
        par = [None] * self.N if want_par else None
        pq = []
        for s, d0 in seeds.items():
            lab[s] = d0
            heapq.heappush(pq, (d0, s))
        done = [False] * self.N
        while pq:
            d, u = heapq.heappop(pq)
            if done[u] or d > lab[u]:
                continue
            done[u] = True
            if stop_label is not None and d > stop_label:
                break
            for (v, w, ts) in adj[u]:
                if ts >= 0:
                    if not use_hops or hop is None:
                        continue
                    w = hop[ts]
                nd = d + w
                if nd < lab[v] - 1e-15:
                    lab[v] = nd
                    if want_par:
                        par[v] = (u, ts)
                    heapq.heappush(pq, (nd, v))
        return lab, par

    def fwd_cost(self, lab):
        return [lab[i] - self.node_level[i] if lab[i] < INF else INF
                for i in range(self.N)]

    def rev_cost(self, lab):
        return [lab[i] + self.node_level[i] if lab[i] < INF else INF
                for i in range(self.N)]

    def min_goal_cost(self, L, alpha, use_hops=True, want_par=False):
        hop = self.hopw(L, alpha) if use_hops else None
        stop = float(self.m + self.Q + 2)
        lab, par = self.dijkstra(forward=True, hop=hop, want_par=want_par,
                                 stop_label=None if want_par else stop,
                                 use_hops=use_hops)
        best, arg = INF, None
        for g in self.goals:
            c = lab[g] - self.node_level[g] if lab[g] < INF else INF
            if c < best:
                best, arg = c, g
        return best, arg, lab, par


# --------------------------------------------------------------------------
# diagnostics
# --------------------------------------------------------------------------
def hub_aggregates(reg, dfwd0, psi0):
    """Per hub: cheapest cross-children single-hop value
       g_hub = min_{u,v in different children} dfwd0(u) + psi0(v),
    plus witness pair.  Returns list aligned with reg.hubs and (aggD, aggP)."""
    nh = len(reg.hubs)
    aggD = [None] * nh   # (min dfwd, argmin state) over subtree
    aggP = [None] * nh
    ghub = [INF] * nh
    gwit = [None] * nh
    for hidx, h in enumerate(reg.hubs):     # postorder: children before parent
        kidD, kidP = [], []
        for rep in h["reps"]:
            if rep[0] == 's':
                s = rep[1]
                kidD.append((dfwd0[s], s))
                kidP.append((psi0[s], s))
            else:
                kidD.append(aggD[rep[1]])
                kidP.append(aggP[rep[1]])
        aggD[hidx] = min(kidD)
        aggP[hidx] = min(kidP)
        best, wit = INF, None
        iD = sorted(range(len(kidD)), key=lambda i: kidD[i][0])[:2]
        iP = sorted(range(len(kidP)), key=lambda i: kidP[i][0])[:2]
        for a in iD:
            for b in iP:
                if a != b and kidD[a][0] + kidP[b][0] < best:
                    best = kidD[a][0] + kidP[b][0]
                    wit = (kidD[a][1], kidP[b][1])
        ghub[hidx] = best
        gwit[hidx] = wit
    return ghub, gwit


def depth_profile(reg, ghub):
    """g(t) = min over hubs at scale t of g_hub (cross-child single-hop value).
    Returns {t: (g, n_hubs, argmin_hub_idx)}."""
    prof = defaultdict(lambda: [INF, 0, None])
    for hidx, h in enumerate(reg.hubs):
        e = prof[h["t"]]
        e[1] += 1
        if ghub[hidx] < e[0]:
            e[0] = ghub[hidx]
            e[2] = hidx
    return {t: tuple(v) for t, v in sorted(prof.items())}


def green_flags(reg):
    """Per hub: does its 3-adic ball contain any tropical/Green singular target
    2^s * a (a in {1, 4, aS202}, s = 0..5) of the S240 class?  Hubs whose ball
    avoids ALL targets constrain even the HYBRID class
        Phi = g(nu3-features towards the targets) + Hoelder remainder,
    because every nu3(c - 2^s a) is CONSTANT on such a ball (all < t and equal),
    so the whole jump must be carried by the Hoelder part."""
    astar = a202_mod(reg.R)
    flags = []
    tgt_cache = {}
    for h in reg.hubs:
        j, t = h["j"], h["t"]
        key = (j, t)
        tg = tgt_cache.get(key)
        if tg is None:
            M = POW3[reg.R + j]
            tg = {(pow(2, s, M) * a) % POW3[t]
                  for a in (1, 4, astar) for s in range(6)}
            tgt_cache[key] = tg
        # residue of the ball: any member's c mod 3^t
        rep = h["reps"][0]
        while rep[0] == 'h':
            rep = reg.hubs[rep[1]]["reps"][0]
        c0 = reg.jc_of[rep[1]][1]
        flags.append((c0 % POW3[t]) in tg)
    return flags


def single_hop_Lstar(reg, ghub, alpha):
    """Smallest L surviving every single-hop refutation:
       L1 = max over hubs with g_hub < m of (m - g_hub) * 3^(alpha * t)."""
    m = reg.m
    L1, arg = 0.0, None
    for hidx, h in enumerate(reg.hubs):
        g = ghub[hidx]
        if g < m:
            need = (m - g) * 3.0 ** (alpha * h["t"])
            if need > L1:
                L1, arg = need, hidx
    return L1, arg


def modulus_table(states_psi, R):
    """Empirical modulus of continuity omega(t) = max |psi(u)-psi(v)| over
    same-level pairs with nu3(c_u - c_v) >= t."""
    by_level = defaultdict(list)
    for (j, c), p in states_psi.items():
        by_level[j].append((c, p))
    out = {}
    tmax_pairs = 0
    t = 0
    while True:
        spread, npairs = 0, 0
        for j, items in by_level.items():
            groups = defaultdict(list)
            for (c, p) in items:
                groups[c % POW3[t]].append(p)
            for v in groups.values():
                if len(v) >= 2:
                    npairs += len(v)
                    spread = max(spread, max(v) - min(v))
        if npairs == 0:
            break
        out[t] = (spread, npairs)
        tmax_pairs = t
        t += 1
        if t > R + 30:
            break
    return out, tmax_pairs


# --------------------------------------------------------------------------
# witness extraction + independent verification
# --------------------------------------------------------------------------
def extract_witness(reg, par, lab, goal_node):
    """Walk parents from goal back to start; collapse hub segments into HOPs."""
    chain = []
    u = goal_node
    while u is not None and par[u] is not None:
        p, ts = par[u]
        chain.append((p, u, ts))
        u = p
    if u != reg.start:
        return None
    chain.reverse()
    # collapse: state -> (hub nodes ... turn t ...) -> state  ==> HOP(t)
    steps = []
    last_state, pend_turn = None, None
    for (a, b, ts) in chain:
        a_is_state = a < reg.n_states
        b_is_state = b < reg.n_states
        if a_is_state:
            last_state = a
        if ts is not None and ts >= 0:
            pend_turn = ts
        if b_is_state:
            if pend_turn is not None:
                steps.append(("HOP", last_state, b, pend_turn))
                pend_turn = None
            elif a_is_state:
                steps.append(("EDGE", a, b, None))
            last_state = b
    return steps


def verify_witness(reg, steps, L, alpha):
    """Re-verify the witness with raw arithmetic, independent of the graph."""
    eng, m = reg.eng, reg.m
    total = 0.0
    ok = True
    detail = []
    cur = reg.start
    if steps and steps[0][1] != reg.start:
        return False, None, ["does not begin at start"]
    for (kind, a, b, t) in steps:
        (ja, ca), (jb, cb) = reg.jc_of[a], reg.jc_of[b]
        if kind == "EDGE":
            found = None
            for (tgt, w) in eng.outgoing_edges(State(ja, ca)):
                if (tgt.j, tgt.c) == (jb, cb):
                    found = w
                    break
            if found is None:
                ok = False
                detail.append(f"EDGE ({ja},..)->({jb},..) NOT a real edge")
                continue
            total += found
            typ = ("one" if jb == ja else
                   ("zero,tau=1(k=-1)" if found == -1 else "zero,tau>=2(k=0)"))
            detail.append(f"EDGE j{ja}->j{jb} kappa={found:+d} [{typ}] "
                          f"tau={TAU[cb % 9]}")
        else:
            if ja != jb:
                ok = False
                detail.append("HOP across levels — invalid")
                continue
            tv = nu3(ca - cb)
            if tv < t:
                ok = False
                detail.append(f"HOP claimed scale {t} but nu3={tv}")
                continue
            cost = L * 3.0 ** (-alpha * tv)
            total += cost
            detail.append(f"HOP  j{ja} nu3(c-c')={tv} cost=L*3^(-a*{tv})="
                          f"{cost:.4g}")
    last = steps[-1][2] if steps else reg.start
    if reg.jc_of[last][1] != 1:
        ok = False
        detail.append("does not end at a goal (c=1)")
    return ok and total < m - 1e-9, total, detail


# --------------------------------------------------------------------------
# frontier
# --------------------------------------------------------------------------
def exact_Lstar(reg, alpha, L1, feas_tol=1e-9, ratio_tol=1.005):
    """Bisection for the exact multi-hop L*(alpha) = smallest feasible L.
    Returns (lo, hi): bracket with lo infeasible, hi feasible (hi/lo<=ratio_tol)."""
    m = reg.m

    def feasible(L):
        best, _, _, _ = reg.min_goal_cost(L, alpha)
        return best >= m - feas_tol

    if feasible(0.0):
        return 0.0, 0.0
    lo = max(L1 * (1 - 1e-9), 1e-9)
    if not feasible(lo):                  # expected: just below single-hop bound
        hi = max(lo * 3, 1.0)
        guard = 0
        while not feasible(hi):
            hi *= 3
            guard += 1
            if guard > 100:
                return lo, INF
    else:                                 # numerically feasible at L1: go down
        hi = lo
        lo = hi / 3
        while feasible(lo) and lo > 1e-12:
            hi = lo
            lo /= 3
    while hi / max(lo, 1e-300) > ratio_tol:
        mid = math.sqrt(lo * hi)
        if feasible(mid):
            hi = mid
        else:
            lo = mid
    return lo, hi


# --------------------------------------------------------------------------
# feasible-Phi shape
# --------------------------------------------------------------------------
def value_shape(reg, values, sample=4000, seed=2421, label="Phi"):
    """Correlate a per-state-node value array with archimedean/dlog features
    (Spearman: robust to the astronomically large hop-padded values)."""
    from scipy.stats import spearmanr
    rng = random.Random(seed)
    idx = [i for i in range(reg.n_states) if values[i] < INF]
    if len(idx) > sample:
        idx = rng.sample(idx, sample)
    rows = []
    for i in idx:
        j, c = reg.jc_of[i]
        k = reg.R + j
        M = POW3[k]
        n = 2 * POW3[k - 1]
        D = fast_dlog(c, k)
        Dc = min(D, n - D)
        rows.append((values[i], j, c.bit_length(), c / M, D / n,
                     Dc.bit_length(), math.log2(Dc + 1)))
    names = ["j", "bitlen(c)", "angle c/3^k", "dlog D/n", "bl(Dc)",
             "log2(Dc+1)"]
    cors = {}
    y = [r[0] for r in rows]
    for col, nm in enumerate(names, start=1):
        x = [r[col] for r in rows]
        rho = spearmanr(x, y).statistic
        cors[nm] = 0.0 if rho != rho else float(rho)
    vals = sorted(y)
    return cors, len(idx), vals[0], vals[-1]


# --------------------------------------------------------------------------
def run(m, Q, cap=6, alphas_exact=(0.5, 1.0, 2.0), do_shape=True):
    print(f"=== GATE A: real-corrector LP  m={m} Q={Q} ===", flush=True)
    reg = Region(m, Q, cap=cap)
    out = {"m": m, "Q": Q, "R": reg.R, "T": reg.T,
           "n_state_nodes": reg.n_states, "n_real_edges": len(reg.redges),
           "n_hubs": reg.n_hubs}

    # headline zero-path fact: 3-adic agreement of THE START with THE GOAL
    astar = a202_mod(reg.R)
    t_sg = nu3(astar - 1)
    print(f"  HEADLINE: nu3(start - goal) = nu3(aS202 - 1) = {t_sg}  (moduli "
          f"depth at j=0 is R={reg.R}).  The start cylinder contains n=1 by "
          f"construction of W202, so Phi(start)>=m, Phi(goal)<=0 and the "
          f"continuity constraint |Phi(start)-Phi(goal)| <= L*3^(-alpha*{t_sg}) "
          f"force L >= m*3^({t_sg}*alpha) with NO path at all.")
    out["nu3_start_minus_1"] = t_sg

    # baseline: no hops (the LP without continuity)
    lab0, _ = reg.dijkstra(forward=True, hop=None, use_hops=False)
    dfwd0 = reg.fwd_cost(lab0)
    labr, _ = reg.dijkstra(forward=False, hop=None, use_hops=False)
    psi0 = reg.rev_cost(labr)
    sp0 = min((dfwd0[g] for g in reg.goals), default=INF)
    print(f"  baseline (no continuity): min real start->goal on region = {sp0} "
          f"(certified T={reg.T})  -> LP w/o (C) {'FEASIBLE' if sp0 >= m else 'BUG!'}")
    out["sp0_region"] = sp0

    # exact-value-function moduli of continuity
    omega_psi, tmax_psi = modulus_table(reg.psi_cone, reg.R)
    omega_d, _ = modulus_table(reg.fdist, reg.R)
    print("  empirical modulus omega_psi(t) (exact cost-to-goal, backward cone):")
    print("    " + "  ".join(f"t={t}:{v[0]}({v[1]}p)" for t, v in omega_psi.items()))
    print("  empirical modulus omega_dist(t) (exact min-kappa-from-start, fwd table):")
    print("    " + "  ".join(f"t={t}:{v[0]}({v[1]}p)" for t, v in
                             list(omega_d.items())[:16]))
    out["omega_psi"] = {str(t): v for t, v in omega_psi.items()}
    out["omega_dist"] = {str(t): v for t, v in omega_d.items()}

    # single-hop depth profile
    ghub, gwit = hub_aggregates(reg, dfwd0, psi0)
    prof = depth_profile(reg, ghub)
    print("  single-hop depth profile g(t) = min cross-pair dfwd(u)+psi(v) "
          "over balls at scale t   [g(t) < m=%d => hop at depth t refutes]" % m)
    for t, (g, nh, hidx) in prof.items():
        mark = ""
        if g < m and gwit[hidx] is not None:
            u, v = gwit[hidx]
            (ju, cu), (jv, cv) = reg.jc_of[u], reg.jc_of[v]
            mark = (f"  <-- BREAKS m: u=(j{ju},dfwd={dfwd0[u]:.0f}) ~mod 3^{t}~ "
                    f"v=(j{jv},psi={psi0[v]:.0f}{',GOAL' if cv == 1 else ''})")
        gs = f"{g:.0f}" if g < INF else "inf"
        print(f"    t={t:>2}: g={gs:>4}  (hubs={nh}){mark}")
    out["g_profile"] = {str(t): (v[0] if v[0] < INF else None, v[1])
                        for t, v in prof.items()}
    deepest_break = max((t for t, (g, _, _) in prof.items() if g < m),
                        default=None)
    print(f"  deepest scale with g(t) < m: t = {deepest_break} "
          f"(of max ball scale {max(prof) if prof else '-'}; moduli depth R+j up to {reg.R + Q})")
    out["deepest_break_t"] = deepest_break

    # HYBRID class (Green/tropical singular part + Hoelder remainder):
    # only hubs whose ball avoids all 18 Green targets constrain the remainder.
    flags = green_flags(reg)
    prof_int = defaultdict(lambda: [INF, 0, None])
    for hidx, h in enumerate(reg.hubs):
        if flags[hidx]:
            continue
        e = prof_int[h["t"]]
        e[1] += 1
        if ghub[hidx] < e[0]:
            e[0] = ghub[hidx]
            e[2] = hidx
    print("  INTERIOR profile g_int(t) (balls avoiding ALL Green targets "
          "2^s*{1,4,aS202} — these break even the hybrid Green+Hoelder class):")
    deep_int = None
    for t in sorted(prof_int):
        g, nh, hidx = prof_int[t]
        mark = ""
        if g < m and gwit[hidx] is not None:
            u, v = gwit[hidx]
            (ju, cu), (jv, cv) = reg.jc_of[u], reg.jc_of[v]
            mark = (f"  <-- BREAKS hybrid: u=(j{ju},dfwd={dfwd0[u]:.0f}) "
                    f"~mod 3^{t}~ v=(j{jv},psi={psi0[v]:.0f})")
            deep_int = t
        gs = f"{g:.0f}" if g < INF else "inf"
        print(f"    t={t:>2}: g_int={gs:>4}  (hubs={nh}){mark}")
    Lh = {}
    for a in (0.5, 1.0, 2.0):
        Lv = 0.0
        for t in sorted(prof_int):
            g = prof_int[t][0]
            if g < m:
                Lv = max(Lv, (m - g) * 3.0 ** (a * t))
        Lh[a] = Lv
    print(f"  hybrid-class single-hop bound: deepest interior break t={deep_int}; "
          f"L_hybrid(alpha) >= " +
          ", ".join(f"{Lh[a]:.4g} (a={a})" for a in (0.5, 1.0, 2.0)))
    out["g_interior"] = {str(t): (v[0] if v[0] < INF else None, v[1])
                         for t, v in sorted(prof_int.items())}
    out["deepest_interior_break_t"] = deep_int
    out["L_hybrid_bound"] = {str(a): v for a, v in Lh.items()}

    # fine single-hop frontier
    fine = {}
    for ia in range(1, 31):
        a = ia / 10.0
        L1, _ = single_hop_Lstar(reg, ghub, a)
        fine[a] = L1
    out["L1_fine"] = {f"{a:.1f}": L for a, L in fine.items()}
    print("  single-hop frontier L1(alpha) (closed form):")
    print("    " + "  ".join(f"a={a:.1f}:L1={fine[a]:.3g}"
                             for a in (0.3, 0.5, 1.0, 1.5, 2.0, 3.0)))

    # exact multi-hop frontier at anchor alphas + witness at the frontier
    out["frontier"] = {}
    for a in alphas_exact:
        t0 = time.time()
        L1, _ = single_hop_Lstar(reg, ghub, a)
        Llo, Ls = exact_Lstar(reg, a, L1)
        teff = math.log(Ls, 3) / a if Ls not in (0.0, INF) else None
        multi = (Ls > L1 * 1.05)
        print(f"  alpha={a}: exact L* = {Ls:.6g} (bracket [{Llo:.4g},{Ls:.4g}])"
              f"   single-hop L1 = {L1:.6g}"
              f"{', MULTI-HOP strictly stronger' if multi else ''}  "
              f"t_eff = log3(L*)/a = {teff and round(teff, 2)} "
              f"[{time.time()-t0:.0f}s]")
        wit_rep = None
        if Ls > 0:
            Lw = Llo * 0.999
            best, argg, lab, par = reg.min_goal_cost(Lw, a, want_par=True)
            if best < m:
                steps = extract_witness(reg, par, lab, argg)
                if steps:
                    okv, tot, detail = verify_witness(reg, steps, Lw, a)
                    nhops = sum(1 for s in steps if s[0] == "HOP")
                    print(f"    witness at L={Lw:.4g} (just below L*): cost="
                          f"{best:.4g} < m={m}, {len(steps)} steps, {nhops} hops"
                          f" — independent re-verification: "
                          f"{'OK' if okv else 'FAILED'} (recomputed {tot:.4g})")
                    for d in detail:
                        print(f"      {d}")
                    wit_rep = {"L": Lw, "cost": best, "verified": okv,
                               "detail": detail}
        out["frontier"][str(a)] = {"L1": L1, "Lstar": Ls, "Llo": Llo,
                                   "t_eff": teff,
                                   "multi_hop_stronger": multi,
                                   "witness": wit_rep}

    # f_emp profile: the weakest data-driven profile (modulus of exact psi)
    tmax = reg.R + reg.Q + 2
    last = omega_psi[tmax_psi][0] if omega_psi else 0
    femp = [float(omega_psi.get(t, (last, 0))[0]) if t <= tmax_psi else float(last)
            for t in range(tmax + 1)]
    lab, _ = reg.dijkstra(forward=True, hop=femp, use_hops=True,
                          stop_label=float(m + Q + 2))
    best_f = min((lab[g] - reg.node_level[g] for g in reg.goals
                  if lab[g] < INF), default=INF)
    fverd = "FEASIBLE (profile not refuted at this scale)" if best_f >= m \
        else f"INFEASIBLE (min path {best_f:.3g} < m)"
    print(f"  f_emp profile (hop cost = empirical modulus of exact psi, "
          f"constant tail {last}): {fverd}")
    out["femp"] = {"profile_head": femp[:10], "tail": last,
                   "min_path": best_f if best_f < INF else None,
                   "feasible": best_f >= m}

    # shape of a feasible Phi (just above the frontier at alpha=1) — and of the
    # raw value function psi0 (what the corrector degenerates to at huge L)
    if do_shape:
        a = 1.0
        Ls = out["frontier"]["1.0"]["Lstar"]
        Luse = max(3 * Ls, 1.0)
        hop = reg.hopw(Luse, a)
        lab, _ = reg.dijkstra(forward=False, hop=hop)
        phistar = reg.rev_cost(lab)
        for vals, lbl in ((phistar, f"Phi* at (a=1,L={Luse:.3g})"),
                          (psi0, "raw value function psi0 (no hops)")):
            cors, nsamp, lo, hi = value_shape(reg, vals)
            print(f"  shape of {lbl}: range [{lo:.3g},{hi:.3g}] on {nsamp} "
                  f"sampled states; Spearman correlations:")
            for k, v in sorted(cors.items(), key=lambda kv: -abs(kv[1])):
                print(f"      rho({k:<12}) = {v:+.3f}")
            out.setdefault("shape", {})[lbl] = cors

    print(flush=True)
    return out


if __name__ == "__main__":
    qs = [int(a) for a in sys.argv[1:]] or [3, 5]
    res = {}
    for Q in qs:
        res[str(Q)] = run(1, Q)
    path = r"C:\Users\benet\Downloads\collatz-admissible-tree\tools\phi_realkam_lp_data.json"
    with open(path, "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    print(f"[data tables written to {path}]")
