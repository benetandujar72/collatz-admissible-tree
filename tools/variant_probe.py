"""
variant_probe.py — Stress-test the project's barrier machinery on the qn+r
VARIANTS with KNOWN behavior, to check the instrument is sound.

Self-contained (does NOT need the Lean build). Reimplements the small pieces
of the project's machinery in the SAME conventions as s202_engine.py /
bridge_probe.py:

  Forward accelerated map (generic):
      T_{q,r}(n) = (q*n + r) / 2^{ν2(q*n+r)}      on positive odd n
  with the per-accelerated-step 2-adic valuation
      τ = ν2(q*n + r)     (the analog of TAU[n%9] = ν2(3n+1) for (q,r)=(3,1)).

  Three quantities the project uses, evaluated forward along real orbits:
    (1) DRIFT (slope/corridor): mean of log2(drop) per odd-step
            log2(drop) = τ - log2(q)         (corridor λ = log2(q))
        descent  ⟺  mean τ > log2(q)  ⟺  mean log2(drop) < 0 multiplicatively
        i.e. the per-step multiplicative factor  q / 2^τ  has geometric mean <1.
    (2) DEFECT sign (the affine 2^A·n = q^? identity proxy): the project's
        integer defect per zero/accelerated step is  D += τ - 2  (it uses the
        integer 2 as a stand-in for log2 q ≈ 1.585 in the 3n+1 case).  Mean
        defect <0  ⟺  the integer corridor predicts NON-descent (growth);
        mean defect >0 ⟹ descent in the integer model.
        (NB: for q=3 the integer "2" is conservative vs log2 3≈1.585, so a
         positive mean defect is a *stronger* statement than mean drift<0.)
    (3) κ-PRECISE weight per accelerated step (InvKappaPreciseEdge):
            τ == 1  →  κ = -1
            τ >= 2  →  κ =  0
        plus, per accelerated step, exactly one inverse "one-edge" is the
        no-progress branch ⟹ +1.  So along a *forward* orbit each accelerated
        odd→odd step contributes   κ_step = +1 + (−1 if τ==1 else 0)
                                          = 0 if τ==1 else +1.
        Mean κ_step > 0 ⟹ barrier sees net positive cost ⟹ predicts descent.
        Mean κ_step ≈ 0 / the cumulative κ failing to grow ⟹ barrier cannot
        certify descent (it "sees" the cycle / divergence).

  KNOWN behavior to reproduce:
    (3,+1): 3n+1 — descent conjectured (open). Drift should be <1 (descent).
    (3,-1): 3n-1 — HAS nontrivial cycles (orbits of 5, 7, 17). Machinery must
            NOT prove global descent; it should find the cycle.
    (5,+1): 5n+1 — orbits believed to DIVERGE. Corridor λ=log2 5≈2.32 > mean
            drop ≈2, drift is the WRONG sign ⟹ predict NON-descent.
"""
from __future__ import annotations
from math import log2
from collections import Counter
from typing import Optional, Tuple, List, Dict


def nu2(x: int) -> int:
    """2-adic valuation of a nonzero integer."""
    if x == 0:
        return 10**9
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


def accel_step(n: int, q: int, r: int) -> Tuple[int, int]:
    """One accelerated odd→odd step T_{q,r}(n)=(q n + r)/2^τ.  Returns (n', τ).
    Mirrors the Lean forward semantics: τ = ν2(q n + r)."""
    v = q * n + r
    t = nu2(v)
    return v >> t, t


def run_orbit(n0: int, q: int, r: int,
              max_steps: int = 100_000,
              cap: int = 10**24) -> Dict:
    """Iterate the accelerated map from odd seed n0.

    Classifies the orbit as:
      'cycle'   : returned to a previously-seen odd value (records the cycle)
      'fixed1'  : reached the trivial fixed point n=1 (for 3n+1: 1→2→1 cycle;
                  we treat the 1-cycle as the trivial attractor)
      'diverge' : exceeded `cap` (apparent divergence) within max_steps
      'budget'  : hit max_steps without resolving (treated as inconclusive)

    Also accumulates the three per-step barrier quantities along the orbit
    UP TO first repeat (so cycle statistics are the cycle's, divergence stats
    are the transient+growth)."""
    seen: Dict[int, int] = {}
    n = n0
    taus: List[int] = []
    order: List[int] = []
    steps = 0
    status = "budget"
    cycle = None
    while steps < max_steps:
        if n in seen:
            status = "cycle"
            start_idx = seen[n]
            cycle = order[start_idx:]
            break
        seen[n] = steps
        order.append(n)
        if n > cap:
            status = "diverge"
            break
        n2, t = accel_step(n, q, r)
        taus.append(t)
        n = n2
        steps += 1
        # trivial attractor: the (q,r)=(3,1) map sends 1→ (3+1)/4 =1, a fixed pt.
        # general small fixed point detection handled by the 'cycle' branch.
    # barrier quantities over the recorded steps
    if taus:
        mean_tau = sum(taus) / len(taus)
        lam = log2(q)
        mean_log2_drop = mean_tau - lam            # (1) drift exponent (want <0)
        gmean_factor = 2 ** (lam - mean_tau)       # geom-mean of q/2^τ (want <1)
        mean_defect = mean_tau - 2.0               # (2) integer defect/step (>0 ⇒ descent)
        kappa_steps = [0 if t == 1 else 1 for t in taus]
        mean_kappa = sum(kappa_steps) / len(kappa_steps)  # (3) κ-precise/step (>0 ⇒ descent)
        tau_hist = Counter(taus)
    else:
        mean_tau = mean_log2_drop = gmean_factor = mean_defect = mean_kappa = float("nan")
        tau_hist = Counter()
    return {
        "n0": n0, "status": status, "steps": steps,
        "cycle": cycle, "cycle_len": (len(cycle) if cycle else None),
        "cycle_min": (min(cycle) if cycle else None),
        "max_n": max(order) if order else n0,
        "mean_tau": mean_tau,
        "mean_log2_drop": mean_log2_drop,
        "gmean_factor": gmean_factor,
        "mean_defect": mean_defect,
        "mean_kappa": mean_kappa,
        "tau_hist": tau_hist,
    }


def survey(q: int, r: int, N: int = 100_000,
           max_steps: int = 100_000, cap: int = 10**24) -> Dict:
    """Survey odd seeds 1,3,5,...,<N for variant (q,r). Aggregates behavior and
    the three barrier quantities pooled over ALL recorded accelerated steps."""
    # pooled step statistics (over every accelerated step of every orbit)
    pooled_tau_sum = 0
    pooled_steps = 0
    pooled_tau_hist: Counter = Counter()
    pooled_kappa_sum = 0
    behavior = Counter()
    distinct_cycles: Dict[tuple, dict] = {}
    smallest_nontrivial_cycle = None
    diverge_examples: List[int] = []
    max_seed_n = 0

    seed = 1
    n_seeds = 0
    while seed < N:
        res = run_orbit(seed, q, r, max_steps=max_steps, cap=cap)
        n_seeds += 1
        behavior[res["status"]] += 1
        # pool step stats
        h = res["tau_hist"]
        for t, c in h.items():
            pooled_tau_hist[t] += c
            pooled_tau_sum += t * c
            pooled_steps += c
            pooled_kappa_sum += (0 if t == 1 else 1) * c
        if res["status"] == "cycle" and res["cycle"]:
            key = tuple(sorted(res["cycle"]))
            if key not in distinct_cycles:
                distinct_cycles[key] = {
                    "len": res["cycle_len"], "min": res["cycle_min"],
                    "elems": sorted(res["cycle"])[:12],
                }
            # smallest nontrivial cycle = cycle not equal to the trivial {1}
            cyc = res["cycle"]
            is_trivial = (set(cyc) == {1})
            if not is_trivial:
                cmin = res["cycle_min"]
                if (smallest_nontrivial_cycle is None
                        or cmin < smallest_nontrivial_cycle["min"]):
                    smallest_nontrivial_cycle = {
                        "min": cmin, "len": res["cycle_len"],
                        "elems": sorted(set(cyc)),
                        "found_from_seed": seed,
                    }
        if res["status"] == "diverge" and len(diverge_examples) < 8:
            diverge_examples.append(seed)
        max_seed_n = max(max_seed_n, res["max_n"])
        seed += 2

    lam = log2(q)
    mean_tau = pooled_tau_sum / pooled_steps if pooled_steps else float("nan")
    mean_log2_drop = mean_tau - lam
    gmean_factor = 2 ** (lam - mean_tau)
    mean_defect = mean_tau - 2.0
    mean_kappa = pooled_kappa_sum / pooled_steps if pooled_steps else float("nan")

    return {
        "q": q, "r": r, "N": N, "n_seeds": n_seeds,
        "lambda": lam,
        "behavior": dict(behavior),
        "distinct_cycles": distinct_cycles,
        "smallest_nontrivial_cycle": smallest_nontrivial_cycle,
        "diverge_examples": diverge_examples,
        "max_n_seen": max_seed_n,
        "pooled_steps": pooled_steps,
        "mean_tau": mean_tau,
        "mean_log2_drop": mean_log2_drop,
        "gmean_factor": gmean_factor,
        "mean_defect": mean_defect,
        "mean_kappa": mean_kappa,
        "tau_hist": dict(sorted(pooled_tau_hist.items())),
    }


def verdict_descent(s: Dict) -> str:
    """Translate the barrier quantities into the project's descent prediction.

    Two regimes are distinguished:
      - if any nontrivial cycle was found, the barrier provably CANNOT certify
        global descent (a finite κ-cost goal exists) — report 'cycles seen'.
      - else use drift: gmean_factor<1 (mean drop>λ) ⟹ predict DESCENT,
        gmean_factor>1 ⟹ predict NON-descent/divergence."""
    if s["smallest_nontrivial_cycle"] is not None:
        return "CYCLE present ⇒ no global descent barrier (instrument sees it)"
    if s["gmean_factor"] < 1.0:
        return "drift<1 ⇒ predicts DESCENT (barrier sign favorable)"
    return "drift>1 ⇒ predicts NON-DESCENT / divergence"


def fmt(x, w=8, p=4):
    try:
        return f"{x:>{w}.{p}f}"
    except Exception:
        return f"{str(x):>{w}}"


def main():
    variants = [(3, +1), (3, -1), (5, +1)]
    N = 100_000
    print("=" * 92)
    print(f"VARIANT PROBE — accelerated map T_(q,r)(n)=(q·n+r)/2^ν2(q·n+r), "
          f"odd seeds 1..{N}")
    print("=" * 92)

    surveys = {}
    for (q, r) in variants:
        s = survey(q, r, N=N)
        surveys[(q, r)] = s
        tag = f"{q}n{'+' if r >= 0 else '-'}{abs(r)}"
        print(f"\n#### variant {tag}   (corridor λ=log2({q})={s['lambda']:.4f})")
        print(f"  seeds surveyed: {s['n_seeds']}   pooled accel-steps: "
              f"{s['pooled_steps']}")
        print(f"  behavior over seeds: {s['behavior']}")
        if s["distinct_cycles"]:
            print(f"  distinct cycles found: {len(s['distinct_cycles'])}")
            for key, info in sorted(s["distinct_cycles"].items(),
                                    key=lambda kv: kv[1]["min"])[:6]:
                print(f"    cycle min={info['min']:>6} len={info['len']:>3} "
                      f"elems={info['elems']}")
        if s["smallest_nontrivial_cycle"]:
            sc = s["smallest_nontrivial_cycle"]
            print(f"  >>> SMALLEST NONTRIVIAL CYCLE: min={sc['min']} "
                  f"len={sc['len']} elems={sc['elems']}")
        if s["diverge_examples"]:
            print(f"  diverge example seeds (orbit exceeded 1e24): "
                  f"{s['diverge_examples']}  (max n seen ~ "
                  f"{s['max_n_seen']:.3e})")
        print(f"  mean τ = {s['mean_tau']:.5f}   "
              f"mean log2(drop)=τ̄−λ = {s['mean_log2_drop']:+.5f}   "
              f"geom-mean factor q/2^τ = {s['gmean_factor']:.5f}")
        print(f"  (2) mean DEFECT  τ̄−2     = {s['mean_defect']:+.5f}  "
              f"({'descent' if s['mean_defect'] > 0 else 'NON-descent'} in integer model)")
        print(f"  (3) mean κ-PRECISE/step  = {s['mean_kappa']:+.5f}  "
              f"({'+ cost ⇒ descent-favorable' if s['mean_kappa'] > 0 else 'no net cost'})")
        print(f"  τ histogram (pooled): {s['tau_hist']}")
        print(f"  ==> PREDICTION: {verdict_descent(s)}")

    # ---- summary table ----
    print("\n" + "=" * 92)
    print("VARIANT RESULTS  (one row per (q,r))")
    print("=" * 92)
    hdr = (f"{'variant':<8} {'behavior':<26} {'λ':>7} {'mean_τ':>8} "
           f"{'drift(τ̄−λ)':>11} {'gm_factor':>10} {'defect(τ̄−2)':>12} "
           f"{'κ/step':>8}")
    print(hdr)
    print("-" * len(hdr))
    for (q, r) in variants:
        s = surveys[(q, r)]
        tag = f"{q}n{'+' if r >= 0 else '-'}{abs(r)}"
        beh = s["behavior"]
        if s["smallest_nontrivial_cycle"]:
            bsum = f"CYCLE min={s['smallest_nontrivial_cycle']['min']}"
        elif beh.get("diverge", 0) > 0:
            bsum = f"DIVERGE x{beh.get('diverge',0)} (+cyc {beh.get('cycle',0)})"
        else:
            bsum = f"all→trivial ({beh})"[:25]
        print(f"{tag:<8} {bsum:<26} {s['lambda']:>7.4f} {s['mean_tau']:>8.4f} "
              f"{s['mean_log2_drop']:>+11.4f} {s['gmean_factor']:>10.4f} "
              f"{s['mean_defect']:>+12.4f} {s['mean_kappa']:>8.4f}")

    # ---- discrimination verdict ----
    print("\n" + "=" * 92)
    print("DISCRIMINATION VERDICT")
    print("=" * 92)
    s31 = surveys[(3, 1)]
    s3m1 = surveys[(3, -1)]
    s51 = surveys[(5, 1)]
    c1 = s31["smallest_nontrivial_cycle"] is None and s31["gmean_factor"] < 1
    c2 = s3m1["smallest_nontrivial_cycle"] is not None
    c3 = (s51["gmean_factor"] > 1) or (s51["behavior"].get("diverge", 0) > 0)
    print(f"  3n+1 : no nontrivial cycle in survey AND drift<1 (descent-favorable)? "
          f"{c1}  [gm={s31['gmean_factor']:.4f}]")
    print(f"  3n-1 : nontrivial cycle detected (instrument sees it)?              "
          f"{c2}  "
          f"[{('min=%d' % s3m1['smallest_nontrivial_cycle']['min']) if c2 else 'NONE'}]")
    print(f"  5n+1 : drift>1 OR divergence (predicts NON-descent)?               "
          f"{c3}  [gm={s51['gmean_factor']:.4f}, "
          f"diverge={s51['behavior'].get('diverge',0)}]")
    allsep = c1 and c2 and c3
    print(f"\n  ==> Machinery separates the three regimes: "
          f"{'YES — all three correct' if allsep else 'PARTLY/NO (see flags)'}")


if __name__ == "__main__":
    main()
