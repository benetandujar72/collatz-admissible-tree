"""
phi_archimedean_gate.py — S241 numerical GATE for the ARCHIMEDEAN potential class.

Context (S240/S241 verdicts): route-B needs a non-inductive uniform-in-m potential
Phi : InvVertex -> Int, edge-monotone for the kappa-precise weights
(one-edge +1, tau=1-zero -1, tau>=2-zero 0), consumed by
S202_kappa_precise_barrier_bounded_from_potential (AnalyticBarrier.lean ~1081).
PROVEN no-gos: Phi cannot factor through c mod 3^t (Reach=units, ReachUnits.lean);
the kappa-induction is circular; the tropical/Green class FAILS (phi_tropical_gate.py:
97-99.9% feature-collisions); the Iwasawa continuous-limit form is refuted.
Convergent diagnosis: any valid Phi must use ARCHIMEDEAN (size) data of the canonical
representative c in [0, 3^(R+j)) — data that does NOT factor through any fixed modulus.

GATE QUESTION: is the exact min-kappa table dist(j,c) (the same tables behind the
verified m=1 certificates) a function of archimedean features of (j, c)?

Features per state (M = 3^(R+j), n = ord(2 mod M) = 2*3^(R+j-1), D = dlog_2(c) in [0,n)):
  f1  bl_c   = bitlength(c)                     (size of the representative)
  f2  angK   = floor(K*c/M), K in {27, 81}      (the "angle" coarsened)
  f3  dangK  = floor(K*D/n), K in {27, 81}      (the dlog VALUE coarsened — how far
                                                 around the cyclic group <2> = (Z/3^k)^*)
      bl_D, bl_Dc = bitlength(D), bitlength(min(D, n-D))   (log-size of dlog; circular
                                                 distance to the goal c=1 <-> D=0)
  f4  j
  f5  top1, top4 = position of the highest nonzero 3-adic digit of (c-1) mod M and
                   (c-4) mod M  (archimedean counterpart of the tropical nu3 = LOWEST digit)

Method (identical to phi_tropical_gate.py):
  1. Regenerate the exact min-kappa-from-start tables dist(j,c) with the same KappaEngine
     that produced the Lean certificates, at the largest threshold T that still certifies.
  2. DETERMINISM TEST per feature set: if states with identical feature vectors carry
     different dist, NO function of those features can express the value table.
     Report collision rate = fraction of states in colliding buckets (same metric as
     the tropical gate), plus max dist-spread.
  3. NEW honesty controls (the tropical gate did not need them; archimedean products
     can shatter the state space):
       - n_buckets and singleton fraction (near-injective feature sets pass vacuously);
       - SHUFFLE CONTROL: collision rate after randomly permuting dist over states
         (mean of 3 shuffles). A determinism "pass" is MEANINGFUL only if the control
         collides massively while the real data does not.
       - R^2 = between-bucket variance fraction of dist (how much of the value table
         the features see even when not deterministic).
  4. If a NON-VACUOUS set has collisions < 5%: attempt an affine fit (normal equations)
     and report max |error| / exact-after-rounding rate.

Honest scope: the table is min-kappa FROM the start; a barrier Phi is a cost-TO-goal
subsolution. Failure of the gate kills "archimedean = exact value function" and strongly
disfavors (but does not formally refute) archimedean subsolutions.
"""
from __future__ import annotations
import random, sys, time
from collections import defaultdict

sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from kappa_precise_probe import KappaEngine
from s202_engine import a202_mod
from fast_dlog import fast_dlog

ANGLE_KS = (27, 81)
SHIFTS = [0, 1, 2, 3, 4, 5]  # tropical baseline, as in phi_tropical_gate.py


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
    """Number of base-3 digits of x >= 0 (0 -> 0). top-digit position = tritlen-1."""
    n = 0
    while x:
        x //= 3
        n += 1
    return n


def best_table(m: int, Q: int, T_hi: int, max_states: int):
    """Largest-T certified table (exact dist on the relevant region) — same as tropical gate."""
    for T in range(T_hi, 0, -1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        res = eng.search_or_certify_bf(max_states=max_states)
        if res["status"] == "barrier_certificate":
            return T, eng, res["states"]
    return None, None, None


def feature_rows(m: int, Q: int, states, R: int):
    """Compute the full archimedean + tropical feature dictionary per state."""
    astar = a202_mod(R)
    rows = []
    t0 = time.time()
    for idx, s in enumerate(states):
        j, c, d = s["j"], s["c"], s["dist"]
        k = R + j
        M = 3 ** k
        n = 2 * 3 ** (k - 1)
        D = fast_dlog(c, k)
        Dc = min(D, n - D)
        f = {
            "j": j,
            "bl_c": c.bit_length(),
            "bl_D": D.bit_length(),
            "bl_Dc": Dc.bit_length(),
            "top1": tritlen((c - 1) % M) - 1,
            "top4": tritlen((c - 4) % M) - 1,
        }
        for K in ANGLE_KS:
            f[f"ang{K}"] = (K * c) // M
            f[f"dang{K}"] = (K * D) // n
        # tropical baseline features (exact same as phi_tropical_gate.py)
        trop = []
        for a in (1, 4, astar):
            for sh in SHIFTS:
                trop.append(v3_capped(c - pow(2, sh, M) * a, M, k))
        f["_trop"] = tuple(trop)
        rows.append((f, d))
        if idx % 50_000 == 0 and idx:
            print(f"    ... features {idx}/{len(states)} ({time.time()-t0:.0f}s)", flush=True)
    return rows


def analyze_set(name, keyfn, rows, n_shuffles=3, seed=241):
    """Determinism + collision + R^2 + shuffle control for one feature set."""
    keys = [keyfn(f) for f, _ in rows]
    dists = [d for _, d in rows]
    n = len(rows)

    def stats(ds_order):
        buckets = defaultdict(list)
        for k, d in zip(keys, ds_order):
            buckets[k].append(d)
        coll = sum(len(v) for v in buckets.values() if len(set(v)) > 1)
        spread = max((max(v) - min(v) for v in buckets.values() if len(set(v)) > 1), default=0)
        mu = sum(ds_order) / n
        sst = sum((d - mu) ** 2 for d in ds_order)
        sse = 0.0
        for v in buckets.values():
            mb = sum(v) / len(v)
            sse += sum((d - mb) ** 2 for d in v)
        r2 = 1.0 - sse / sst if sst > 0 else 1.0
        singles = sum(1 for v in buckets.values() if len(v) == 1)
        return len(buckets), coll, spread, r2, singles

    nb, coll, spread, r2, singles = stats(dists)
    rng = random.Random(seed)
    ctrl = []
    for _ in range(n_shuffles):
        sh = dists[:]
        rng.shuffle(sh)
        _, c2, _, r2s, _ = stats(sh)
        ctrl.append((c2, r2s))
    ctrl_coll = sum(c for c, _ in ctrl) / len(ctrl)
    ctrl_r2 = sum(r for _, r in ctrl) / len(ctrl)
    vacuous = (ctrl_coll / n) < 0.20  # control barely collides -> partition shatters
    flag = "VACUOUS(shattered)" if vacuous and coll / n < 0.05 else (
        "PASS-candidate" if coll / n < 0.05 else "FAIL")
    print(f"  {name:<28} buckets={nb:>7} singl={100.0*singles/nb:5.1f}%  "
          f"coll={100.0*coll/n:6.2f}% (ctrl {100.0*ctrl_coll/n:6.2f}%)  "
          f"spread={spread}  R2={r2:6.3f} (ctrl {ctrl_r2:5.3f})  -> {flag}")
    return {"name": name, "n_buckets": nb, "coll": coll / n, "ctrl_coll": ctrl_coll / n,
            "spread": spread, "r2": r2, "ctrl_r2": ctrl_r2, "flag": flag}


def signal_tables(rows, feats=("dang27", "ang27", "bl_Dc", "bl_c")):
    """Mean dist by feature value (marginal signal), as in the tropical gate."""
    for ft in feats:
        by = defaultdict(list)
        for f, d in rows:
            by[f[ft]].append(d)
        sig = {v: (round(sum(ds) / len(ds), 2), len(ds)) for v, ds in sorted(by.items())}
        print(f"  signal {ft} -> (mean dist, n): {sig}")


def affine_fit(rows, feat_names):
    """Pure-python least squares dist ~ affine(features). Returns (coefs, maxerr, exact%)."""
    X = [[1.0] + [float(f[k]) for k in feat_names] for f, _ in rows]
    y = [float(d) for _, d in rows]
    p = len(feat_names) + 1
    # normal equations
    A = [[sum(X[i][a] * X[i][b] for i in range(len(X))) for b in range(p)] for a in range(p)]
    b = [sum(X[i][a] * y[i] for i in range(len(X))) for a in range(p)]
    # gaussian elimination with partial pivot
    for col in range(p):
        piv = max(range(col, p), key=lambda r: abs(A[r][col]))
        if abs(A[piv][col]) < 1e-12:
            continue
        A[col], A[piv] = A[piv], A[col]
        b[col], b[piv] = b[piv], b[col]
        for r in range(p):
            if r != col and A[r][col] != 0:
                fct = A[r][col] / A[col][col]
                A[r] = [A[r][k] - fct * A[col][k] for k in range(p)]
                b[r] = b[r] - fct * b[col]
    coef = [b[i] / A[i][i] if abs(A[i][i]) > 1e-12 else 0.0 for i in range(p)]
    errs = [abs(sum(c * x for c, x in zip(coef, X[i])) - y[i]) for i in range(len(X))]
    exact = sum(1 for i in range(len(X))
                if round(sum(c * x for c, x in zip(coef, X[i]))) == y[i])
    return coef, max(errs), exact / len(X)


def gate(m: int, Q: int, T_hi: int = 5, max_states: int = 400_000):
    t0 = time.time()
    T, eng, states = best_table(m, Q, T_hi, max_states)
    if states is None:
        print(f"m={m} Q={Q}: no certified table up to T={T_hi} — skip")
        return
    R = eng.R
    n = len(states)
    print(f"=== m={m} Q={Q}  (R={R}, certified T={T}, states={n}) ===", flush=True)
    rows = feature_rows(m, Q, states, R)
    print(f"  [features done in {time.time()-t0:.0f}s]", flush=True)

    dvals = sorted({d for _, d in rows})
    print(f"  dist values present: {dvals}")

    sets = [
        ("j (baseline)",            lambda f: (f["j"],)),
        ("j+bl_c",                  lambda f: (f["j"], f["bl_c"])),
        ("j+ang27",                 lambda f: (f["j"], f["ang27"])),
        ("j+ang81",                 lambda f: (f["j"], f["ang81"])),
        ("j+dang27",                lambda f: (f["j"], f["dang27"])),
        ("j+dang81",                lambda f: (f["j"], f["dang81"])),
        ("j+bl_D+bl_Dc",            lambda f: (f["j"], f["bl_D"], f["bl_Dc"])),
        ("j+top1+top4",             lambda f: (f["j"], f["top1"], f["top4"])),
        ("arch-core j,bl,a81,d81,Dc", lambda f: (f["j"], f["bl_c"], f["ang81"],
                                                 f["dang81"], f["bl_Dc"])),
        ("arch-FULL (all above)",   lambda f: (f["j"], f["bl_c"], f["ang27"], f["ang81"],
                                               f["dang27"], f["dang81"], f["bl_D"],
                                               f["bl_Dc"], f["top1"], f["top4"])),
        ("tropical (S240 baseline)", lambda f: (f["j"],) + f["_trop"]),
        ("tropical+arch-FULL",      lambda f: (f["j"], f["bl_c"], f["ang27"], f["ang81"],
                                               f["dang27"], f["dang81"], f["bl_D"],
                                               f["bl_Dc"], f["top1"], f["top4"]) + f["_trop"]),
    ]
    results = [analyze_set(name, fn, rows) for name, fn in sets]
    signal_tables(rows)

    # fit attempt for any meaningful pass
    for res, (name, fn) in zip(results, sets):
        if res["flag"] == "PASS-candidate":
            feats = ["j", "bl_c", "ang81", "dang81", "bl_Dc", "bl_D", "top1", "top4"]
            coef, maxerr, exact = affine_fit(rows, feats)
            print(f"  AFFINE FIT on {feats}: maxerr={maxerr:.3f} exact-after-round={100*exact:.1f}%")
            print(f"    coefs (1,{','.join(feats)}) = {[round(c,4) for c in coef]}")
            break

    # verdict
    arch_full = next(r for r in results if r["name"].startswith("arch-FULL"))
    trop = next(r for r in results if r["name"].startswith("tropical (S240"))
    both = next(r for r in results if r["name"].startswith("tropical+arch"))
    print(f"  GATE VERDICT m={m} Q={Q}: arch-FULL coll={100*arch_full['coll']:.1f}% "
          f"(R2={arch_full['r2']:.3f}, ctrl-R2={arch_full['ctrl_r2']:.3f}); "
          f"tropical coll={100*trop['coll']:.1f}%; combined coll={100*both['coll']:.1f}%")
    if arch_full["coll"] > 0.05:
        print("    -> FAIL: dist is NOT a function of the archimedean features; "
              "no function of (size, angle, dlog-value, top-digit, j) expresses the value table.")
    elif arch_full["flag"] == "VACUOUS(shattered)":
        print("    -> INCONCLUSIVE-VACUOUS: determinism holds only because the feature "
              "product shatters the state space (control also ~collision-free).")
    else:
        print("    -> PASS determinism: archimedean features SEE the value table; fit above.")
    return results


if __name__ == "__main__":
    qs = [int(a) for a in sys.argv[1:]] or [3, 5]
    for Q in qs:
        gate(1, Q)
        print(flush=True)
