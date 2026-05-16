"""
S233 ψ-validator: independent verification of the external collaborator's
local potential candidate

    H(v) = 2*delta+(v) - rho-(v) + (j(v) - Q) + psi(c(v) mod 3^h)

on the BF observed graph. We do NOT trust the collaborator's miner
output blindly. We re-derive psi by solving the linear program

    For every observed edge (v, v', kappa):
        H(v) - H(v') <= kappa
    H(start) = m
    H(goal)  <= 0

with the parametric form above. The unknowns are the 3^h values of psi.
Existence of a feasible psi is decidable by single-source shortest-path
on the difference graph of the modular classes.

If psi exists, we report:
  - the resulting psi function;
  - the tightest edge (smallest slack);
  - whether H(start) - H(goal) >= m holds (the conclusion we need).

If psi does NOT exist, we report the negative cycle that obstructs it.

This validates the *observed-graph* claim only. A global (over-cover)
certificate is the next step (S234) and is NOT addressed here.
"""

from __future__ import annotations
import sys
from collections import defaultdict
from typing import Dict, List, Tuple, Any

sys.path.insert(0, ".")
from s230_dual_search import S230Engine, kappa_precise, kappa_coarse


def nu3(n: int, cap: int = 64) -> int:
    if n == 0:
        return cap
    v = 0
    while n % 3 == 0 and v < cap:
        n //= 3
        v += 1
    return v


def candidate_H_linear(j: int, c: int, Q: int, R_plus_j_cap: int,
                       a_dp: int, a_rm: int, a_j: int,
                       a_jQ: int) -> int:
    """Linear part of H, without psi: a_dp * delta+ + a_rm * rho- +
       a_j * j + a_jQ * (j - Q)."""
    dp = nu3(c - 1, R_plus_j_cap)
    rm = nu3(c + 1, R_plus_j_cap)
    return a_dp * dp + a_rm * rm + a_j * j + a_jQ * (j - Q)


def psi_feasibility(m: int, Q: int, kappa_fn, h: int,
                    a_dp: int, a_rm: int, a_j: int, a_jQ: int,
                    max_states: int = 200_000,
                    **kwargs) -> Dict[str, Any]:
    """Test whether H = (linear) + psi(c mod 3^h) admits a feasible psi
    on the observed BF graph for (m, Q, kappa).

    Algorithm. Define L(v) := linear part of H at v. The observed-edge
    constraint H(v) - H(v') <= kappa(e) becomes

        psi(c(v) mod 3^h) - psi(c(v') mod 3^h)
            <= kappa(e) - (L(v) - L(v')).

    Index psi by its class in {0, ..., 3^h - 1}. Build a directed graph
    G_psi with an edge from class_v to class_{v'} weighted by
    (kappa(e) - L(v) + L(v')). Feasibility of `psi(a) - psi(b) <= w`
    is equivalent to absence of a negative cycle in G_psi. We compute
    shortest paths from a virtual source (Bellman-Ford); negative
    cycles surface as detectable updates after |V| - 1 rounds.

    We also handle the boundary conditions
        H(start) = m  =>  psi(class_start) = m - L(start),
        H(goal)  <= 0 =>  psi(class_goal) <= -L(goal),
    by including a virtual source with two extra edges.
    """
    # Accept either a freshly-computed certificate (default) or a
    # precomputed one passed via kwargs (saves recomputing BF closure
    # across many psi_feasibility() calls on the same (m,Q)).
    eng = kwargs.get("_engine_cache")
    cert = kwargs.get("_cert_cache")
    if eng is None or cert is None:
        eng = S230Engine(m=m, Q=Q, kappa_fn=kappa_fn)
        cert = eng.search(max_states=max_states)
    if cert["status"] != "barrier":
        return {"status": "search_" + cert["status"],
                "msg": "did not produce a closed BF certificate"}

    rows = cert["dist_table"]
    state_by_jc = {(r["j"], r["c"]): r for r in rows}
    R = 22 * m + 2
    cap = R + Q

    mod_h = 3 ** h
    class_start = eng.target % mod_h

    # Build the inequality system: psi(class_a) - psi(class_b) <= w
    # Collect edges of the BF closure graph by re-running outgoingEdges.
    print(f"\n=== S233 psi-validator: m={m}, Q={Q}, "
          f"kappa={kappa_fn.__name__}, h={h} ===")
    print(f"  linear ansatz: H = {a_dp}*d+ + {a_rm}*r- + "
          f"{a_j}*j + {a_jQ}*(j-Q) + psi(c mod 3^{h})")
    print(f"  graph: {len(rows):,} states observed.")

    # Differential constraints: list of (a, b, w) meaning psi[a] - psi[b] <= w
    constraints: List[Tuple[int, int, int]] = []
    edge_count = 0
    edges_off_graph_skipped = 0
    for r in rows:
        from s202_engine import State
        v = State(j=r["j"], c=r["c"])
        L_v = candidate_H_linear(v.j, v.c, Q, cap, a_dp, a_rm, a_j, a_jQ)
        class_v = v.c % mod_h
        for (vp, kappa_val) in eng.outgoing_edges(v):
            # We only constrain edges whose target is in the observed
            # graph; targets outside are pruned and irrelevant for the
            # *observed* potential check (this is exactly what the
            # collaborator's miner does — the observed-graph claim).
            if (vp.j, vp.c) not in state_by_jc:
                edges_off_graph_skipped += 1
                continue
            L_vp = candidate_H_linear(vp.j, vp.c, Q, cap,
                                      a_dp, a_rm, a_j, a_jQ)
            class_vp = vp.c % mod_h
            w = kappa_val - L_v + L_vp
            # psi(class_v) - psi(class_vp) <= w
            constraints.append((class_v, class_vp, w))
            edge_count += 1
    print(f"  observed edges in graph: {edge_count}; "
          f"edges to non-observed targets: {edges_off_graph_skipped}")

    # CRITICAL: anchor goal vertices. For every j' in [0, Q] the abstract
    # vertex (j', 1) is a potential goal of the path. The barrier requires
    # H(j', 1) <= 0 for every such j'. Express as a constraint involving
    # psi(1 mod 3^h):
    #   H(j', 1) = a_j * j' + a_jQ * (j' - Q) + a_dp * delta+(1, cap)
    #              + a_rm * rho-(1+1, cap) + psi(1 mod mod_h)
    # rho-(1+1=2, cap) = nu3(2, cap) = 0; delta+(1-1=0, cap) = cap.
    # We add psi(1 mod mod_h) - psi(VIRTUAL_TOP) <= -L(j', 1) for j'=Q
    # (the worst case). This represents H(goal_Q) <= 0.
    # We bind psi(VIRTUAL_TOP) = 0 implicitly via the virtual source.
    class_goal = 1 % mod_h
    # The worst goal is at j' = Q.
    worst_goal_j = Q
    # L(worst_goal) under the ansatz (using cap for the valuation).
    # nu3(1 - 1) = cap-like (we use a_dp * cap conservatively; in the
    # ansatz delta+ of c=1 is large, but we treat it as cap = R+j).
    # NOTE: for the standard ansatz a_dp=0 of the refined candidate,
    # this term vanishes. We keep the formula general:
    dp_at_goal = cap  # nu3(0) -> cap
    rm_at_goal = 0    # nu3(2) = 0
    L_goal_worst = (a_dp * dp_at_goal + a_rm * rm_at_goal
                    + a_j * worst_goal_j
                    + a_jQ * (worst_goal_j - Q))
    # H(goal_Q) = L_goal_worst + psi(class_goal). Require <= 0
    # => psi(class_goal) <= -L_goal_worst.
    # We model this as psi[class_goal] - psi[VIRTUAL_TOP] <= -L_goal_worst
    # but since virtual source assigns 0, we add a constraint by directly
    # bounding the class. Implementation: use a sentinel class index = -1
    # representing "the bound 0" and add edges:
    #   psi[-1] = 0 (anchored)
    #   psi[class_goal] - psi[-1] <= -L_goal_worst
    VIRTUAL_BOUND = -1
    constraints.append((class_goal, VIRTUAL_BOUND, -L_goal_worst))
    # Similarly anchor H(start) >= m, i.e., L_start + psi(class_start) >= m,
    # so psi(class_start) >= m - L_start, equivalently
    #   psi[-1] - psi[class_start] <= L_start - m  (negation of >=).
    L_start_anchor = candidate_H_linear(
        0, eng.target, Q, cap, a_dp, a_rm, a_j, a_jQ)
    constraints.append((VIRTUAL_BOUND, class_start, L_start_anchor - m))
    print(f"  added 2 boundary constraints: "
          f"psi[goal_class={class_goal}] <= {-L_goal_worst} and "
          f"psi[start_class={class_start}] >= {m - L_start_anchor}.")

    # Boundary anchors (start info — class_start already defined above).
    L_start = candidate_H_linear(0, eng.target, Q, cap,
                                 a_dp, a_rm, a_j, a_jQ)
    # H(start) = m  =>  psi(class_start) = m - L_start
    psi_start_value = m - L_start
    print(f"  start = (0, {eng.target}); class_start = {class_start}; "
          f"L(start) = {L_start}; required psi(class_start) = "
          f"{psi_start_value}.")

    goal_classes = set()
    for r in rows:
        if r["c"] == 1:
            L_goal = candidate_H_linear(r["j"], 1, Q, cap,
                                        a_dp, a_rm, a_j, a_jQ)
            class_goal = 1 % mod_h
            goal_classes.add((class_goal, L_goal, r["j"]))
    if goal_classes:
        print(f"  goal classes in observed graph (j, L(goal), required "
              f"psi <= -L): {sorted(goal_classes)}")
    else:
        print("  (no goal vertex observed in graph — barrier is trivial.)")

    # Solve the difference system  psi[a] - psi[b] <= w  via the
    # standard virtual-source Bellman-Ford. Every class appearing in
    # any constraint is reachable from a virtual source S with edge
    # weight 0 (constraint  psi[a] - psi[S] <= 0 = trivially imposable).
    # No negative cycle <=> system feasible. After |V| rounds, dist
    # is a witness solution; before applying the start-anchor we shift
    # uniformly so psi[class_start] = m - L(start).
    classes_involved = set()
    g_adj: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
    for (a, b, w) in constraints:
        g_adj[b].append((a, w))
        classes_involved.add(a)
        classes_involved.add(b)
    classes_involved.add(class_start)
    # VIRTUAL_BOUND (= -1) is anchored at 0 implicitly through the virtual
    # Bellman-Ford source: it stays at 0 forever.

    # Bellman-Ford from virtual source: psi[k] = 0 for all classes,
    # then relax. The number of rounds bounds the longest path.
    psi: Dict[int, int] = {k: 0 for k in classes_involved}
    V = len(classes_involved)
    relaxed_any = True
    rounds = 0
    while relaxed_any and rounds < V:
        relaxed_any = False
        rounds += 1
        for b, neighbours in g_adj.items():
            for (a, w) in neighbours:
                new_val = psi[b] + w
                if new_val < psi[a]:
                    psi[a] = new_val
                    relaxed_any = True

    # Negative-cycle check: any further relaxation possible?
    neg_cycle = False
    for b, neighbours in g_adj.items():
        for (a, w) in neighbours:
            if psi[b] + w < psi[a]:
                neg_cycle = True
                break
        if neg_cycle:
            break
    if neg_cycle:
        print("  RESULT: psi infeasible (negative cycle in difference graph).")
        return {"status": "infeasible", "reason": "negative_cycle"}

    # Shift so psi[class_start] = psi_start_value (this is a free
    # additive translation that preserves all difference constraints).
    shift = psi_start_value - psi[class_start]
    for k in psi:
        psi[k] += shift

    # Verify the boundary condition H(goal) <= 0.
    boundary_ok = True
    if 1 % mod_h in psi:
        for (cg, Lg, jg) in goal_classes:
            H_goal = Lg + psi[cg]
            if H_goal > 0:
                boundary_ok = False
                print(f"  RESULT: H(goal) = {H_goal} > 0 at j={jg} "
                      f"(class={cg}); barrier conclusion FAILS.")
    if not boundary_ok:
        return {"status": "boundary_fail"}

    # Verify all edge constraints under the computed psi.
    tightest = None
    for (a, b, w) in constraints:
        if a in psi and b in psi:
            slack = w - (psi[a] - psi[b])
            if tightest is None or slack < tightest[3]:
                tightest = (a, b, w, slack)
    print(f"  psi defined on {len(psi)} of {mod_h} classes; "
          f"tightest edge slack = {tightest[3] if tightest else 'n/a'}")

    # Show H(start) - H(goal) to confirm the barrier conclusion.
    H_start = L_start + psi.get(class_start, 0)
    H_goal_max = max((Lg + psi.get(cg, 0)) for (cg, Lg, jg) in goal_classes) \
                  if goal_classes else 0
    print(f"  H(start) = {H_start}, max H(goal) = {H_goal_max}, "
          f"H(start) - max H(goal) = {H_start - H_goal_max}")
    print(f"  m = {m}; barrier requires H(start) - H(goal) >= m: "
          f"{'PASS' if H_start - H_goal_max >= m else 'FAIL'}.")

    return {
        "status": "feasible",
        "m": m, "Q": Q, "h": h,
        "linear_ansatz": (a_dp, a_rm, a_j, a_jQ),
        "psi": dict(sorted(psi.items())),
        "tightest_slack": tightest[3] if tightest else None,
        "H_start": H_start,
        "H_goal_max": H_goal_max,
        "barrier_margin": H_start - H_goal_max,
    }


if __name__ == "__main__":
    # The collaborator uses kappa(e) = +1 one / -1 zero (no tau split),
    # which is kappa_COARSE in our nomenclature.
    print("Validating collaborator's candidate A: "
          "H = 2*d+ - r- + (j-Q) + psi(c mod 27).  Case (m=1, Q=3), kappa_coarse.")
    res_A = psi_feasibility(
        m=1, Q=3, kappa_fn=kappa_coarse,
        h=3, a_dp=2, a_rm=-1, a_j=0, a_jQ=1,
    )
    print("\nValidating collaborator's candidate B: "
          "H = d+ - r- + 4*(j-Q) + psi(c mod 9).  Case (m=2, Q=3), kappa_coarse.")
    res_B = psi_feasibility(
        m=2, Q=3, kappa_fn=kappa_coarse,
        h=2, a_dp=1, a_rm=-1, a_j=0, a_jQ=4,
    )

    # Independent control: pure psi(c mod 27), no linear part.
    print("\nControl: pure psi(c mod 27), no linear part.  Case (m=1, Q=3), coarse.")
    res_C = psi_feasibility(
        m=1, Q=3, kappa_fn=kappa_coarse,
        h=3, a_dp=0, a_rm=0, a_j=0, a_jQ=0,
    )

    # Does candidate A extend to (m=1, Q=5)?
    print("\nExtending candidate A to (m=1, Q=5), kappa_coarse — does h=3 still suffice?")
    res_D = psi_feasibility(
        m=1, Q=5, kappa_fn=kappa_coarse,
        h=3, a_dp=2, a_rm=-1, a_j=0, a_jQ=1,
    )

    # Sanity-check: with kappa_precise (the form we have stronger reasons
    # to believe in), does any candidate work?
    print("\nKappa_precise control: candidate A on (m=1, Q=3), kappa_precise.")
    res_E = psi_feasibility(
        m=1, Q=3, kappa_fn=kappa_precise,
        h=3, a_dp=2, a_rm=-1, a_j=0, a_jQ=1,
    )

    print("\n=== Cross-validation summary ===")
    for label, res in [("A (1,3, h=3, coarse)", res_A),
                       ("B (2,3, h=2, coarse)", res_B),
                       ("C (1,3, h=3 pure psi, coarse)", res_C),
                       ("D (1,5, h=3, coarse)", res_D),
                       ("E (1,3, h=3, precise)", res_E)]:
        print(f"  {label:<32} status={res['status']:<15} "
              f"margin={res.get('barrier_margin','-')}")
