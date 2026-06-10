"""
phi_quotient_refuter.py — S241: RIGOROUS feature-class refutation via the quotient graph.

The dist-collision gates (phi_tropical_gate.py, phi_archimedean_gate.py) are heuristic:
"dist is not a function of the features" disfavors but does not refute feature-class
SUBSOLUTIONS. This tool gives the exact criterion on the explored subgraph.

PRINCIPLE. Let F : state -> feature-vector and suppose Phi = g(F(v)) is a valid
slice potential for S202_kappa_precise_barrier_bounded_from_potential:
    (E)  Phi(v) <= kappa + Phi(v')   for every kappa-precise edge v -> v' in the slice,
    (G)  Phi(goal) <= 0,             (S)  Phi(InvStart m) >= m.
Project every REAL edge v -> v' (weight kappa) onto buckets B(v) -> B(v'). Any chain of
quotient edges B0 -> B1 -> ... -> Bk with B0 = B(start) and Bk containing a goal yields
    m <= Phi(B0) <= k1 + Phi(B1) <= ... <= (sum kappa_i) + Phi(Bk) <= sum kappa_i,
because Phi is constant on buckets (each step is realized by a REAL edge whose source
merely shares the bucket of the previous step's target). Hence:

    quotient min kappa-cost (start-bucket -> any goal-bucket) < m
        ==>  NO function of these features is a valid slice potential.   [RIGOROUS]

A negative quotient cycle on a start->goal route gives cost -infinity: same conclusion.
Conversely a PASS (cost >= m) is only a necessary-condition pass on the explored
subgraph (the full graph has more states/edges, hence more constraints) — and is
VACUOUS if the partition shatters into singletons (quotient ~= real graph, where the
cost >= m is just the certified barrier itself).

Monotonicity: refuting the FINEST partition (full feature vector) refutes every
function of every subset of those features.

Output per (m, Q, partition): quotient |V|, |E|, min cost or -inf, witness chain
(buckets, kappas, realizing real edges), verdict.
"""
from __future__ import annotations
import sys, time
from collections import defaultdict, deque

sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from kappa_precise_probe import KappaEngine
from s202_engine import State, a202_mod
from fast_dlog import fast_dlog

ANGLE_KS = (27, 81)
SHIFTS = [0, 1, 2, 3, 4, 5]
GOAL = ("GOAL",)


def v3_capped(x: int, M: int, cap: int) -> int:
    x %= M
    if x == 0:
        return cap
    v = 0
    while x % 3 == 0 and v < cap:
        x //= 3
        v += 1
    return v


def tritlen(x: int) -> int:
    n = 0
    while x:
        x //= 3
        n += 1
    return n


_feat_cache = {}


def features(R: int, j: int, c: int):
    key = (j, c)
    f = _feat_cache.get(key)
    if f is not None:
        return f
    k = R + j
    M = 3 ** k
    n = 2 * 3 ** (k - 1)
    D = fast_dlog(c, k)
    Dc = min(D, n - D)
    f = {
        "j": j,
        "c9": c % 9,
        "c27": c % 27,
        "bl_c": c.bit_length(),
        "bl_D": D.bit_length(),
        "bl_Dc": Dc.bit_length(),
        "top1": tritlen((c - 1) % M) - 1,
        "top4": tritlen((c - 4) % M) - 1,
    }
    for K in ANGLE_KS:
        f[f"ang{K}"] = (K * c) // M
        f[f"dang{K}"] = (K * D) // n
    astar = a202_mod(R)
    trop = []
    for a in (1, 4, astar):
        for sh in SHIFTS:
            trop.append(v3_capped(c - pow(2, sh, M) * a, M, k))
    f["_trop"] = tuple(trop)
    _feat_cache[key] = f
    return f


ARCH_KEYS = ("j", "bl_c", "ang27", "ang81", "dang27", "dang81",
             "bl_D", "bl_Dc", "top1", "top4")

PARTITIONS = [
    ("tropical (S240 class)",     lambda f: (f["j"],) + f["_trop"]),
    ("arch-FULL",                 lambda f: tuple(f[k] for k in ARCH_KEYS)),
    ("arch-FULL + c mod 9",       lambda f: tuple(f[k] for k in ARCH_KEYS) + (f["c9"],)),
    ("arch-FULL + c mod 27",      lambda f: tuple(f[k] for k in ARCH_KEYS) + (f["c27"],)),
    ("tropical + arch-FULL",      lambda f: tuple(f[k] for k in ARCH_KEYS) + f["_trop"]),
    ("trop + arch + c mod 27",    lambda f: tuple(f[k] for k in ARCH_KEYS) + f["_trop"] + (f["c27"],)),
]


def build_real_edges(m: int, Q: int, T_hi: int = 5, max_states: int = 400_000):
    """Largest-T certified table + ALL outgoing kappa-edges of table states."""
    for T in range(T_hi, 0, -1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        res = eng.search_or_certify_bf(max_states=max_states)
        if res["status"] == "barrier_certificate":
            break
    else:
        return None
    R = eng.R
    states = [(s["j"], s["c"]) for s in res["states"]]
    dist = {(s["j"], s["c"]): s["dist"] for s in res["states"]}
    edges = []  # (j,c, j',c', kappa)
    t0 = time.time()
    for i, (j, c) in enumerate(states):
        for (tgt, w) in eng.outgoing_edges(State(j, c)):
            edges.append((j, c, tgt.j, tgt.c, w))
        if i % 50_000 == 0 and i:
            print(f"    ... edges {i}/{len(states)} ({time.time()-t0:.0f}s)", flush=True)
    return {"R": R, "T": T, "eng": eng, "states": states, "dist": dist, "edges": edges}


def backward_region(m: int, Q: int, R: int, cap: int = 4, max_states: int = 400_000):
    """Exact cost-to-goal psi on the backward co-reachable region.

    Every vertex y=(j, c) has EXACTLY two in-neighbors in the kappa-precise graph
    (cf. two_pow_tau_mul_mod9, ReachUnits.lean):
      one-edge pred  : (j,   2^{tau(c%9)} * c  mod 3^(R+j))            kappa = +1
      zero-edge pred : (j-1, (2^{tau(c%9)}*c - 1)/3) for j >= 1        kappa = -1 if
                       tau(c%9)==1 else 0   (2^{tau}c == 1 mod 3 ALWAYS)
    Backward SPFA from all goals (j,1), 0<=j<=Q, with the optimistic cut
    psi_label - j < cap (at level j at most j more backward zero-steps, each >= -1).
    The real graph has no negative cycles (j monotone; fixed-j cycles are all-one-edge,
    kappa=+1 each), so labels converge to exact psi on the region."""
    from s202_engine import TAU
    t0 = time.time()
    psi = {}
    qq = deque()
    inq = set()
    for j in range(Q + 1):
        g = (j, 1)
        psi[g] = 0
        qq.append(g)
        inq.add(g)
    bedges = []  # (j_pred, c_pred, j, c, kappa) — real edges, discovered backward
    seen_edges = set()
    while qq:
        (j, c) = qq.popleft()
        inq.discard((j, c))
        d = psi[(j, c)]
        if d - j >= cap:        # optimistic cut: cannot stay below cap
            continue
        if len(psi) > max_states:
            print(f"    backward region truncated at {len(psi)} states")
            break
        M = 3 ** (R + j)
        t = TAU[c % 9]
        preds = [((j, (pow(2, t, M) * c) % M), 1)]
        if j >= 1:
            v = (pow(2, t, M) * c) % M
            # v == 1 mod 3 always (two_pow_tau_mul_mod9); pred at level j-1
            preds.append(((j - 1, (v - 1) // 3), -1 if t == 1 else 0))
        for (p, w) in preds:
            if p[1] == 1:
                continue  # do not relax goals (psi=0 fixed; paths through goal pointless)
            ek = (p, (j, c))
            if ek not in seen_edges:
                seen_edges.add(ek)
                bedges.append((p[0], p[1], j, c, w))
            nd = d + w
            if nd - p[0] >= cap:
                continue
            if nd < psi.get(p, 10 ** 9):
                psi[p] = nd
                if p not in inq:
                    qq.append(p)
                    inq.add(p)
    hist = defaultdict(int)
    for v in psi.values():
        hist[v] += 1
    print(f"  backward region: {len(psi)} states, {len(bedges)} real edges, "
          f"psi histogram {dict(sorted(hist.items()))}, cap={cap} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    return psi, bedges


def quotient_min_cost(data, partname, keyfn, m: int):
    """SPFA on the quotient multigraph; negative-cycle => -inf. Returns verdict dict."""
    R = data["R"]
    t0 = time.time()
    # quotient nodes and edges (min kappa per bucket pair kept implicitly by relaxing all)
    qedges = defaultdict(lambda: None)  # (B,B') -> (kappa, real edge witness)
    bucket_of = {}

    def B(j, c):
        key = (j, c)
        b = bucket_of.get(key)
        if b is None:
            if c == 1:
                b = GOAL
            else:
                b = keyfn(features(R, j, c))
            bucket_of[key] = b
        return b

    nodes = set()
    for (j, c, j2, c2, w) in data["edges"]:
        b1, b2 = B(j, c), B(j2, c2)
        nodes.add(b1); nodes.add(b2)
        cur = qedges[(b1, b2)]
        if cur is None or w < cur[0]:
            qedges[(b1, b2)] = (w, (j, c, j2, c2))
    start_b = B(0, a202_mod(R))
    if start_b == GOAL:
        raise RuntimeError("start is goal?")
    adj = defaultdict(list)
    for (b1, b2), (w, wit) in qedges.items():
        adj[b1].append((b2, w, wit))
    nV, nE = len(nodes), len(qedges)

    # SPFA with relaxation-count negative-cycle detection
    INF = float("inf")
    dist = {start_b: 0}
    parent = {}
    cnt = defaultdict(int)
    qq = deque([start_b])
    inq = {start_b}
    neg_node = None
    while qq:
        u = qq.popleft()
        inq.discard(u)
        if u == GOAL:
            continue  # goal is a sink for our purpose (paths THROUGH goal not needed)
        du = dist[u]
        for (v, w, wit) in adj[u]:
            nd = du + w
            if nd < dist.get(v, INF):
                dist[v] = nd
                parent[v] = (u, w, wit)
                cnt[v] += 1
                if cnt[v] > nV + 1:
                    neg_node = v
                    qq.clear()
                    break
                if v not in inq:
                    qq.append(v)
                    inq.add(v)
    # does a negative cycle taint the goal? (reachable from neg_node -> GOAL)
    neg_inf = False
    if neg_node is not None:
        seen = {neg_node}
        st = [neg_node]
        while st:
            u = st.pop()
            if u == GOAL:
                neg_inf = True
                break
            for (v, _, _) in adj[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
    cost = -INF if neg_inf else dist.get(GOAL, INF)

    # witness chain
    chain = []
    if not neg_inf and GOAL in dist:
        u = GOAL
        while u != start_b and u in parent:
            pu, w, wit = parent[u]
            chain.append((pu, u, w, wit))
            u = pu
        chain.reverse()
    verdict = ("REFUTED(-inf, negative quotient cycle reaches GOAL)" if neg_inf else
               "REFUTED(cost<m)" if cost < m else
               "no-refutation (necessary-condition pass on explored subgraph)")
    print(f"  {partname:<26} |V|={nV:>6} |E|={nE:>7}  min start->goal = "
          f"{'-inf' if neg_inf else cost}   (m={m})  -> {verdict}  [{time.time()-t0:.0f}s]")

    # the canonical bucket corrector psi_B(b) = min quotient cost b -> GOAL
    # (reverse SPFA). When min start->goal >= m, Phi := psi_B (with +inf |-> any
    # large value) is an EXPLICIT feasible feature-potential on the explored subgraph.
    if not neg_inf:
        radj = defaultdict(list)
        for (b1, b2), (w, wit) in qedges.items():
            radj[b2].append((b1, w))
        INF2 = float("inf")
        psiB = {GOAL: 0}
        qq2 = deque([GOAL])
        inq2 = {GOAL}
        while qq2:
            u = qq2.popleft()
            inq2.discard(u)
            du = psiB[u]
            for (v, w) in radj[u]:
                nd = du + w
                if nd < psiB.get(v, INF2):
                    psiB[v] = nd
                    if v not in inq2:
                        qq2.append(v)
                        inq2.add(v)
        finite = {b: d for b, d in psiB.items() if b != GOAL}
        if finite:
            vals = sorted(finite.values())
            print(f"    bucket corrector psi_B: finite on {len(finite)}/{nV} buckets, "
                  f"range [{vals[0]}, {vals[-1]}], psi_B(start)={psiB.get(start_b, 'inf')}")
            if partname == "arch-FULL":
                # shape: min psi_B by (bl_c band) and by (bl_Dc band) — ARCH_KEYS order
                # ("j","bl_c","ang27","ang81","dang27","dang81","bl_D","bl_Dc","top1","top4")
                by_blc, by_bldc = defaultdict(list), defaultdict(list)
                for b, d in finite.items():
                    by_blc[b[1]].append(d)
                    by_bldc[b[7]].append(d)
                print("    psi_B by bl_c  (min,mean,n): " + str({
                    k: (min(v), round(sum(v)/len(v), 1), len(v))
                    for k, v in sorted(by_blc.items())}))
                print("    psi_B by bl_Dc (min,mean,n): " + str({
                    k: (min(v), round(sum(v)/len(v), 1), len(v))
                    for k, v in sorted(by_bldc.items())}))
    if chain:
        ks = [w for (_, _, w, _) in chain]
        print(f"    optimal quotient chain: length {len(chain)}, kappas={ks}")
        # show the bucket-jump points: consecutive chain entries where the realizing
        # source vertex differs from the previous realizing target (the collisions used)
        prev_tgt = None
        jumps = 0
        for (b1, b2, w, (j, c, j2, c2)) in chain:
            if prev_tgt is not None and (j, c) != prev_tgt:
                jumps += 1
                print(f"      BUCKET-JUMP: ...->({prev_tgt[0]},{prev_tgt[1]}) ~same bucket~ "
                      f"({j},{c})->...")
            prev_tgt = (j2, c2)
        print(f"    bucket-jumps used: {jumps}")
    return {"part": partname, "cost": cost, "nV": nV, "nE": nE, "neg_inf": neg_inf}


def pair_witness(data, partname, keyfn, m: int):
    """Cheap interpretable companion: a single bucket collision u (forward, realizable
    start->u cost dist(u)) with v (backward, realizable v->goal cost psi(v)) such that
    dist(u) + psi(v) < m already refutes the class:
       m <= Phi(start) <= dist(u) + Phi(u) = dist(u) + Phi(v) <= dist(u) + psi(v)."""
    R = data["R"]
    best = None
    fwd_min = {}
    for (j, c), d in data["dist"].items():
        if c == 1:
            continue
        b = keyfn(features(R, j, c))
        if d < fwd_min.get(b, (10 ** 9,))[0]:
            fwd_min[b] = (d, j, c)
    n_coll = 0
    for (j, c), p in data["psi"].items():
        if c == 1:
            continue
        b = keyfn(features(R, j, c))
        if b in fwd_min:
            n_coll += 1
            d, ju, cu = fwd_min[b]
            tot = d + p
            if best is None or tot < best[0]:
                best = (tot, (ju, cu, d), (j, c, p))
    print(f"    fwd/bwd bucket collisions: {n_coll} backward states share a bucket "
          f"with some forward state")
    if best is not None and best[0] < m:
        tot, (ju, cu, d), (jv, cv, p) = best
        print(f"    PAIR WITNESS: dist(u)+psi(v) = {d}+{p} = {tot} < m={m}  "
              f"u=({ju},{cu}) v=({jv},{cv}) share a {partname} bucket")
    elif best is not None:
        print(f"    best single-collision pair: dist+psi = {best[0]} (>= m, no 1-hop refutation)")
    else:
        print(f"    no forward/backward bucket collision at all")
    return best


def run(m: int, Q: int, cap: int = 4):
    print(f"=== quotient refuter: m={m} Q={Q} ===", flush=True)
    data = build_real_edges(m, Q)
    if data is None:
        print("  no certified table — skip")
        return
    print(f"  table: R={data['R']} certified T={data['T']} states={len(data['states'])} "
          f"real edges={len(data['edges'])}", flush=True)
    psi, bedges = backward_region(m, Q, data["R"], cap=cap)
    data["psi"] = psi
    data["edges"] = data["edges"] + bedges
    print(f"  combined constraint graph: {len(data['edges'])} real edges", flush=True)
    out = []
    for name, fn in PARTITIONS:
        out.append(quotient_min_cost(data, name, fn, m))
        pair_witness(data, name, fn, m)
    return out


if __name__ == "__main__":
    # usage: phi_quotient_refuter.py [Q] [cap]
    qs = [int(a) for a in sys.argv[1:2]] or [3, 5]
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    for Q in qs:
        run(1, Q, cap=cap)
        print(flush=True)
