"""
S238 sweep — parallel version with multiprocessing.Pool.

Speedup pattern:
  * Per (m, Q), the Bellman-Ford closure (`eng.search`) is computed
    ONCE in the master process.
  * The grid of coefficients (a, b, c, d) at each h is then dispatched
    to a worker pool (default: all CPU cores). Workers reconstruct a
    lightweight engine locally (cheap, ~0.01s) and run the
    difference-system LP for their assigned (a, b, c, d, h).
  * The master collects results via `Pool.imap_unordered` and stops
    as soon as any worker reports a feasible solution per (m, Q).

Why no TPU: workers do exact-integer Bellman-Ford on sparse difference
graphs. The bottleneck is Python loop overhead per LP, not matrix
arithmetic. A TPU cannot accelerate this. Multi-core CPU does, in a
near-linear way (one LP per core in parallel).

Windows compatibility: uses `__main__` guard and `spawn`-safe worker
function defined at module top level.
"""

from __future__ import annotations
import sys, os, json, time
from typing import Dict, Any, List, Tuple, Optional
from multiprocessing import Pool, cpu_count

sys.path.insert(0, ".")
from s230_dual_search import S230Engine, kappa_precise
from s202_engine import State


# ============================================================
# Worker function — must be top-level for Windows spawn.
# ============================================================

def _worker_check(args):
    """One LP run. Args = (m, Q, h, a, b, c, d, rows_pickle).
    Returns (a, b, c, d, h, status, margin) or None on error.
    """
    (m, Q, h, a, b, c, d, rows) = args
    try:
        # Re-import locally for safety under 'spawn'.
        from s230_dual_search import S230Engine, kappa_precise
        from s233_psi_validator import psi_feasibility
        eng = S230Engine(m=m, Q=Q, kappa_fn=kappa_precise)
        # Build a synthetic "barrier" cert so psi_feasibility skips its
        # own eng.search() call.
        cert = {"status": "barrier", "dist_table": rows,
                "m": m, "Q": Q, "R": 22 * m + 2, "threshold": m}
        import contextlib, io
        @contextlib.contextmanager
        def _silenced():
            saved = sys.stdout
            sys.stdout = io.StringIO()
            try: yield
            finally: sys.stdout = saved
        with _silenced():
            res = psi_feasibility(
                m=m, Q=Q, kappa_fn=kappa_precise, h=h,
                a_dp=a, a_rm=b, a_j=c, a_jQ=d,
                max_states=200_000,
                _engine_cache=eng, _cert_cache=cert,
            )
        status = res.get("status", "unknown")
        if status == "feasible":
            psi_sparse = {z: int(v) for z, v in res.get("psi", {}).items()}
            return {
                "a": a, "b": b, "c": c, "d": d, "h": h,
                "status": "feasible",
                "margin": res.get("barrier_margin"),
                "tightest_slack": res.get("tightest_slack"),
                "psi_sparse": psi_sparse,
            }
        return {"a": a, "b": b, "c": c, "d": d, "h": h,
                "status": status, "margin": None}
    except Exception as e:
        return {"a": a, "b": b, "c": c, "d": d, "h": h,
                "status": f"error:{e}", "margin": None}


# ============================================================
# Master.
# ============================================================

def grid():
    for c in range(-1, 3):
        for d in range(-1, 3):
            for a in range(-3, 2):
                for b in range(-3, 2):
                    yield (a, b, c, d)


FRONTIER = [(1, 3), (1, 5), (2, 3), (2, 6), (3, 6)]
H_SCHEDULE = [22, 23, 25, 28, 30]


def find_one_parallel(m: int, Q: int, pool, max_states: int = 200_000):
    t0 = time.time()
    print(f"\n--- (m={m}, Q={Q}) ---", flush=True)
    print(f"  Precomputing BF closure ...", flush=True)
    eng = S230Engine(m=m, Q=Q, kappa_fn=kappa_precise)
    cert = eng.search(max_states=max_states)
    if cert["status"] != "barrier":
        print(f"  BF did not close: {cert['status']}; skip.")
        return None
    print(f"  BF closure: {cert['states_seen']:,} states "
          f"({time.time()-t0:.1f}s).", flush=True)
    rows = cert["dist_table"]

    n_tried = 0
    for h in H_SCHEDULE:
        tasks = [(m, Q, h, a, b, c, d, rows)
                 for (a, b, c, d) in grid()]
        print(f"  h={h}: dispatching {len(tasks)} LPs to pool "
              f"(workers={pool._processes}) ...", flush=True)
        first_hit = None
        for r in pool.imap_unordered(_worker_check, tasks, chunksize=4):
            n_tried += 1
            if r and r.get("status") == "feasible":
                first_hit = r
                print(f"  HIT: a_dp={r['a']}, a_rm={r['b']}, "
                      f"a_j={r['c']}, a_jQ={r['d']}, h={r['h']}, "
                      f"margin={r['margin']}, "
                      f"slack={r['tightest_slack']}  "
                      f"[total {n_tried} LPs, {time.time()-t0:.1f}s]",
                      flush=True)
                break
        if first_hit:
            return (first_hit["a"], first_hit["b"], first_hit["c"],
                    first_hit["d"], first_hit["h"], first_hit["margin"],
                    first_hit["psi_sparse"])
        print(f"  h={h}: no hit in {len(tasks)} LPs "
              f"({time.time()-t0:.1f}s)", flush=True)
    print(f"  (m={m}, Q={Q}): NO HIT up to h={H_SCHEDULE[-1]} "
          f"({n_tried} LPs, {time.time()-t0:.1f}s)")
    return None


def export_psi_sparse(m: int, Q: int, hit, out_dir: str):
    (a, b, c, d, h, margin, psi_sparse) = hit
    from s202_engine import a202_mod
    R = 22 * m + 2
    mod_h = 3 ** h
    start_z = a202_mod(R) % mod_h
    goal_z = 1 % mod_h
    psi_str = {str(z): int(v) for z, v in sorted(psi_sparse.items())}
    payload = {
        "m": m, "Q": Q, "h": h, "mode": "precise",
        "candidate_ansatz":
            f"H(v) = {a}*d+ + ({b})*r- + {c}*j + {d}*(j-Q) + "
            f"psi(c mod 3^{h})",
        "linear_coefficients": {
            "a_delta_plus": a, "a_rho_minus": b,
            "a_j": c, "a_jQ": d,
        },
        "kappa_mode": "precise_tau_aware",
        "rho_minus_cap": "R + j = 22m+2+j (sweep semantics)",
        "psi_storage": "sparse — absent classes mean psi = 0",
        "psi_classes_defined": len(psi_str),
        "psi_classes_total_mod_h": mod_h,
        "barrier_margin": margin,
        "endpoint": {
            "start_z": start_z, "goal_z": goal_z,
            "psi_at_start": psi_sparse.get(start_z, 0),
            "psi_at_goal": psi_sparse.get(goal_z, 0),
            "psi_gap": (psi_sparse.get(start_z, 0)
                        - psi_sparse.get(goal_z, 0)),
        },
        "psi": psi_str,
    }
    fn = os.path.join(
        out_dir, f"psi_m{m}_Q{Q}_h{h}_precise_parallel.json")
    with open(fn, "w") as f:
        json.dump(payload, f, indent=2)
    print(f"    wrote {fn}", flush=True)
    return fn


def main():
    n_workers = max(1, cpu_count() - 1)
    out_dir = "s238_tables_parallel"
    os.makedirs(out_dir, exist_ok=True)
    print(f"\n=== S238 parallel sweep ===")
    print(f"Workers: {n_workers} (of {cpu_count()} cores)")
    print(f"Frontier: {FRONTIER}")
    print(f"H schedule: {H_SCHEDULE}\n")
    t0_all = time.time()
    summary = []
    with Pool(n_workers) as pool:
        for (m, Q) in FRONTIER:
            hit = find_one_parallel(m, Q, pool)
            if hit:
                fn = export_psi_sparse(m, Q, hit, out_dir)
                (a, b, c, d, h, margin, _) = hit
                summary.append({"m": m, "Q": Q, "coefs": (a, b, c, d),
                                "h": h, "margin": margin, "file": fn})
            else:
                summary.append({"m": m, "Q": Q, "result": "NO_HIT"})

    print(f"\n=== Summary (total {time.time()-t0_all:.1f}s) ===")
    for row in summary:
        if "coefs" in row:
            (a, b, c, d) = row["coefs"]
            print(f"  m={row['m']:>2}, Q={row['Q']:>2}: "
                  f"a_dp={a:>2}, a_rm={b:>2}, a_j={c:>2}, a_jQ={d:>2}, "
                  f"h={row['h']:>2}, margin={row['margin']}")
        else:
            print(f"  m={row['m']:>2}, Q={row['Q']:>2}: NO HIT")
    with open(os.path.join(out_dir, "summary.json"), "w") as f:
        json.dump(summary, f, indent=2, default=str)


if __name__ == "__main__":
    main()
