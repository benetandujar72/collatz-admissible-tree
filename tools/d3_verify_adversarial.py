"""
D3 ADVERSARIAL VERIFICATION of the adequacy verdict.

Goal: try hardest to BREAK the verdict's three load-bearing claims:
  (A) Lemma A "forcing": kappa1>=m provable for the prefix  <=>  mid is m-precise.
  (B) Lemma B "refuted at root": the witness path has NO interior m-precise vertex,
      so the only m-precise mid is the goal (empty suffix), killing BlockBoundaryExists.
  (C) Lemma C "circular salvage" + the SALVAGE WINDOW: KappaPathSplit with mid=trap
      is satisfiable; the proposed replacement (a prefix-floor P(mid) valid at
      non-m-precise mid) is the crux. Is P(mid) ALSO refuted by the witness?

The question asks specifically:
  - Is the verdict SOUND?
  - Is it CIRCULAR (does it secretly assume a kappa1>=m bound it can't obtain)?
  - Is the PROPOSED OBLIGATION (the corrected one) ALSO refuted by the trap witness?

We re-run the witness numerically at a faithful-but-tractable scale and then
TEST candidate replacement obligations against it.

Faithful scale: real Lean uses R=22(m+1)+2, M=3^(R+1), aS202=1+3^22.
We keep aS202 EXACT and take small m. mod-9 shield + dlog cocycle are scale invariant.

KEY DISTINCTION we make precise here (the steelman):
  KappaPathSplit's OUTPUT does NOT require m-precision. So as a bare Prop, on the
  witness it is SATISFIABLE with mid=trap (prefix kappa = ladderlen >= m, suffix = 1
  deep edge, kappa2=1). We confirm this. The verdict's claim is NOT that KappaPathSplit
  is false; it is that the only PROOF of kappa1>=m (the IH) needs m-precision, which
  mid=trap lacks. We test whether a non-IH prefix floor that the verdict proposes as
  the salvage is refuted by the witness.
"""

import json


def tau_from_mod9(r9):
    # repo tau: depends on c%9; units mod 3 only. class1->2, class4->2, class7->4,
    # class2->1, class5->1, class8->1.
    return {1: 2, 4: 2, 7: 4, 2: 1, 5: 1, 8: 1}[r9]


def two_pow_mod9(e):
    return pow(2, e % 6, 9)


def build_witness(m, W=None):
    """Construct the ACTUAL witness path as a list of (j, c, kappa_in) vertices,
    at a tractable modulus, using the EXACT real start residue aS202=1+3^22.
    Returns the full vertex sequence start..goal and per-edge kappa.

    To make the ladder FINITE and explicit we pick a small concrete dlog W (>=2,
    W%6==4) rather than the astronomical real W; the mod-9 SHIELD and the
    kappa-accounting are identical for any such W. (At real scale W~3^21.)
    """
    R = 22 * (m + 1) + 2
    Mexp = R + 1
    M = 3 ** Mexp
    aS202 = 1 + 3 ** 22
    start_c = aS202 % M

    # entry zero-edge: s1.c = (3*aS202+1) * 2^{-4} mod M ; weight tau(s1)-2.
    inv16 = pow(16, -1, M)
    s1c = ((3 * aS202 + 1) * inv16) % M
    assert s1c % 9 == 7, (s1c % 9)
    # s1 = 2^W % M for some W with W%6==4. Pick the SMALLEST concrete W>=4, W%6==4
    # whose residue 2^W % M is a class-7 unit -- but to make the path land exactly on
    # s1c we instead drive the ladder from s1c directly by repeated *2^{-tau} (the
    # one-edge inverse step) DOWN to the trap c=4. This is the genuine ladder.
    #
    # One-edge step v->v' has v.c ≡ 2^tau(v'.c) * v'.c, i.e. v'.c ≡ v.c * 2^{-tau(v'.c)}.
    # tau(v'.c) depends on v'.c%9 which depends on v.c%9 (period). We descend in dlog.
    #
    # Easiest faithful realization: work in dlog space. s1c = 2^W % M. We don't know W
    # cheaply, but we DO know W%6=4. Build the ladder in dlog units d = W, stepping
    # d -> d - tau where tau alternates 2 (class4 target) / 4 (class7 target) until d=2.
    # We just need a concrete finite W>=2, W%6==4 to exhibit a finite faithful ladder;
    # the SHIELD/kappa facts are independent of which such W. Default W=4 (shortest);
    # pass larger W (W%6==4) to model a LONG ladder (real scale W~3^21).
    if W is None:
        W = 4
    assert W % 6 == 4 and W >= 2

    # ladder vertices in dlog space: d = 4 (class7,=s1-analog), then -> 2 (class4=trap).
    # Edge d=4 -> d=2 is a one-edge with tau(target class4)=2, kappa +1. Then trap=d2.
    # Ladder descent in dlog units. Per Lean LadderExists:
    #   ladder_step_seven: source d%6==4 (class7) --tau=2--> d-2 (class4)
    #   ladder_step_four : source d%6==2 (class4) --tau=4--> d-4 (class7)
    # So step size = 2 if source class7 (d%6==4), = 4 if source class4 (d%6==2).
    # The edge weight (kappa) is +1 each (one-edge). Terminus d=2 (class4=trap).
    ladder_ds = []
    d = W
    while True:
        ladder_ds.append(d)
        if d == 2:
            break
        if d % 6 == 4:        # class 7 -> step 2
            d = d - 2
        elif d % 6 == 2:      # class 4 -> step 4
            d = d - 4
        else:
            raise ValueError(f"off-ladder dlog residue d%6={d%6}")
        assert d >= 2

    # Now assemble the explicit path with real residues mod M:
    # start (j=0, c=aS202)  --zero edge kappa0-->  v(d=W) ... but v(d=W) has c=2^W % M.
    # Note: the entry edge lands on s1c, and s1c == 2^W % M ONLY if W is the true dlog.
    # For the FINITE faithful model we REDEFINE the chain to start at v0 = 2^W % M
    # (a genuine class-7 unit) reached from start by a zero-edge of the SAME kappa 0;
    # the entry kappa is 0 regardless of which class-7 unit (tau=4 => kappa=tau-2=... wait)
    #
    # CAREFUL: entry zero-edge kappa. InvEdgeZero weight = tau(target.c) - 2; kappa class:
    #   tau==1 -> kappa -1 ; tau>=2 -> kappa 0. s1 is class7 => tau=4 => kappa 0. Good.
    # The deep edge trap->goal is a ONE-edge (kappa +1), tau(goal.c=1)=2.

    verts = []  # (j, c, kappa_into_this_vertex, label)
    verts.append((0, start_c, None, "start(InvStart(m+1))"))
    j = 1
    # entry zero-edge to first ladder vertex (class 7). Use real residue 2^W % M.
    for idx, dd in enumerate(ladder_ds):
        c = pow(2, dd, M)
        if idx == 0:
            verts.append((j, c, 0, f"s1=ladder[d={dd}] (entry zero-edge,k=0)"))
        else:
            verts.append((j, c, 1, f"ladder[d={dd}] (one-edge,k=+1)"))
    # trap is the last ladder vertex (d=2, c=4). deep edge to goal c=1.
    verts.append((j, 1, 1, "goal(c=1) (deep one-edge,k=+1)"))
    return dict(R=R, Mexp=Mexp, M=M, aS202=aS202, W=W,
                ladder_ds=ladder_ds, verts=verts)


def m_precise(v_c, v_j, m, M):
    """v=(j,c) m-precise iff c ≡ 1 (mod 3^(22m+2+j)). (projMPrecise m mid is IsGoal of
    the projection at level-m precision.) Necessary: c%9==1 when 22m+2+j>=2."""
    mod = 3 ** (22 * m + 2 + v_j)
    return (v_c % mod) == (1 % mod)


def analyze(m, W=None):
    w = build_witness(m, W=W)
    M = w["M"]
    verts = w["verts"]
    rep = {"m": m, "R": w["R"], "W": w["W"], "ladder_ds": w["ladder_ds"]}

    # kappa accounting
    kappas = [v[2] for v in verts if v[2] is not None]
    total_kappa = sum(kappas)
    rep["per_edge_kappa"] = kappas
    rep["total_kappa"] = total_kappa
    rep["num_edges"] = len(kappas)

    # classes mod 9
    rep["classes_mod9"] = [v[1] % 9 for v in verts]

    # m-precision of every vertex
    prec = []
    for (j, c, k, lab) in verts:
        prec.append((lab, m_precise(c, j, m, M)))
    rep["mprecise_flags"] = prec
    mprec_idx = [i for i, (j, c, k, lab) in enumerate(verts) if m_precise(c, j, m, M)]
    rep["mprecise_indices"] = mprec_idx
    rep["mprecise_labels"] = [verts[i][3] for i in mprec_idx]

    # ---- CLAIM B: only m-precise vertex is the goal (the LAST), giving empty suffix ----
    goal_idx = len(verts) - 1
    rep["B_only_mprecise_is_goal"] = (mprec_idx == [goal_idx])

    # ---- CLAIM (BlockBoundaryExists refuted): need an ON-PATH mid that is m-precise
    # AND has suffix kappa2 >= 1 (i.e. mid != goal). On the witness:
    # candidate m-precise mids = mprec_idx. For kappa2>=1 need mid strictly before goal.
    block_satisfiable = False
    for i in mprec_idx:
        if i < goal_idx:
            # suffix kappa = sum of kappas after vertex i
            suffix_k = sum(verts[t][2] for t in range(i + 1, len(verts)) if verts[t][2] is not None)
            if suffix_k >= 1:
                block_satisfiable = True
    rep["BlockBoundaryExists_satisfiable_on_witness"] = block_satisfiable  # expect False

    # ---- STEELMAN / SALVAGE WINDOW: KappaPathSplit (output has NO m-precision).
    # Is there ANY mid (m-precise or not) with prefix_kappa>=m AND suffix_kappa>=1?
    # If yes, KappaPathSplit is SATISFIABLE on the witness (true as a bare Prop).
    kps_witness = None
    for i in range(1, goal_idx + 1):  # mid = vertex i (can be interior or trap), suffix nonempty
        prefix_k = sum(verts[t][2] for t in range(0, i + 1) if verts[t][2] is not None)
        suffix_k = sum(verts[t][2] for t in range(i + 1, len(verts)) if verts[t][2] is not None)
        if prefix_k >= m and suffix_k >= 1:
            kps_witness = dict(mid_index=i, mid_label=verts[i][3],
                               mid_mod9=verts[i][1] % 9,
                               mid_mprecise=m_precise(verts[i][1], verts[i][0], m, M),
                               prefix_kappa=prefix_k, suffix_kappa=suffix_k)
            break
    rep["KappaPathSplit_satisfiable_on_witness"] = kps_witness  # expect a witness with mid=trap, non-mprecise

    # ---- THE DECISIVE TEST: re-run the witness against the PROPOSED replacement obligation.
    # Verdict's proposed salvage = a PREFIX-FLOOR P(mid): "every kappa-path InvStart(m+1)->mid
    # has kappa1 >= m", to be proven for NON-m-precise mid (covering mid=trap).
    #
    # Q from the user: "is the proposed obligation ALSO refuted by the trap witness?"
    #
    # We must check P(mid) AT the witness's salvage split point mid=trap:
    #   does the actual prefix InvStart(m+1)->trap on THIS witness have kappa1 >= m?
    # If kappa1(prefix to trap) < m for some m, then P(trap) is FALSE -> obligation refuted.
    # If kappa1(prefix to trap) >= m always, P is not refuted by THIS witness (only the
    # question of PROVABILITY remains -> circularity, not refutation).
    if kps_witness is not None:
        rep["proposed_obligation_prefix_kappa_to_mid"] = kps_witness["prefix_kappa"]
        rep["proposed_obligation_refuted_by_witness"] = (kps_witness["prefix_kappa"] < m)
    else:
        rep["proposed_obligation_refuted_by_witness"] = "N/A (no KPS witness)"

    # ---- CIRCULARITY PROBE: does proving P(trap) (kappa1>=m for the prefix to trap)
    # require bounding the SAME astronomical floor as the barrier, on a sub-path with
    # no m-level goal waypoint? Check: are there ANY m-precise vertices strictly inside
    # the prefix InvStart(m+1)->trap (excluding endpoints)? If none, the IH cannot fire
    # anywhere along the prefix -> P(trap) has no inductive substructure.
    if kps_witness is not None:
        i = kps_witness["mid_index"]
        interior_mprec = [t for t in mprec_idx if 0 < t < i]
        rep["mprecise_interior_of_prefix_to_mid"] = interior_mprec  # expect [] -> no IH hook
        rep["prefix_has_no_IH_hook"] = (interior_mprec == [])
    return rep


def summary_line(rep):
    return dict(
        m=rep["m"], W=rep["W"], ladder_len=len(rep["ladder_ds"]),
        total_kappa=rep["total_kappa"],
        classes_mod9=rep["classes_mod9"],
        mprecise_indices=rep["mprecise_indices"],
        B_only_mprecise_is_goal=rep["B_only_mprecise_is_goal"],
        BlockBoundaryExists_satisfiable=rep["BlockBoundaryExists_satisfiable_on_witness"],
        KPS_satisfiable=rep["KappaPathSplit_satisfiable_on_witness"],
        proposed_obligation_refuted_by_witness=rep["proposed_obligation_refuted_by_witness"],
        prefix_has_no_IH_hook=rep.get("prefix_has_no_IH_hook"),
    )


if __name__ == "__main__":
    print("### SHORT LADDER (W=4): faithful minimal witness")
    for m in (1, 2, 3):
        print(json.dumps(summary_line(analyze(m, W=4)), indent=2, default=str))
        print("-" * 50)
    print()
    print("### LONG LADDER (W=22, W%6==4): models a multi-step ladder")
    # W=22 -> dlog descent 22->20->16->14->10->8->4->2 : ladder length scales.
    for m in (1, 2, 3):
        print(json.dumps(summary_line(analyze(m, W=22)), indent=2, default=str))
        print("-" * 50)
    print()
    print("### REAL-SCALE-ish kappa: prefix-to-trap kappa vs m, for growing W")
    # For each m, find the kappa of the prefix InvStart->trap and compare to m.
    for W in (4, 22, 40, 100, 1000):
        if W % 6 != 4:
            continue
        rep = analyze(3, W=W)
        kps = rep["KappaPathSplit_satisfiable_on_witness"]
        print(dict(W=W, ladder_len=len(rep["ladder_ds"]),
                   prefix_kappa_to_mid=(kps["prefix_kappa"] if kps else None),
                   mid_label=(kps["mid_label"] if kps else None),
                   proposed_obligation_refuted=rep["proposed_obligation_refuted_by_witness"]))
