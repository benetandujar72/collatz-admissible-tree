"""
sturmian_gate.py — GATE B (S242): Sturmian / mechanical structure of OPTIMAL
kappa-paths in the certified slices.

QUESTION. Route-B's large-Q hope: if the kappa-optimal corridor-riding paths
are asymptotically MECHANICAL (Sturmian) words of slope tied to log2(3) =
[1;1,1,2,2,3,1,5,...], the barrier reduces to substitution-dynamics
combinatorics.  Heuristic: for a pure-zero (Syracuse) stretch the kappa-cost
is  kappa = #(tau=1 zeros)*(-1) = A - 2q  (A = sum tau), and the bilateral
corridor q*log2(3) < A < 2q would force optimal tau-partial-sums to hug
ceil(n*log2 3), i.e. the tau-word should look like the Beatty word of slope
log2(3) (symbols {1,2}, freq(2) = log2(3)-1 ~ 0.585, factor complexity n+1).

DATA.  From the SAME KappaEngine tables behind the verified m=1 certificates:
  * forward family: argmin kappa-paths start -> cheap frontier states
    (predecessor chains through the exact BF table; every vertex has exactly
    two in-neighbors — ReachUnits — so reconstruction is deterministic up to
    ties; we extract BOTH tie-break policies and dedupe);
  * backward family: psi-optimal chains cone-state -> goal through the exact
    backward cone of phi_quotient_refuter;
  * control: uniform random admissible walks in the same graph (same start,
    same slice);
  * reference: the Beatty word of slope log2(3) chopped to the same lengths,
    and the real S202 witness word W202.

TESTS per family:
  (a) tau-frequencies (full word and zero-edge subword), zero/one frequency,
      kappa-type frequency; mean tau on zero-edges vs log2(3) ~ 1.585;
  (b) factor complexity p(n) (distinct length-n factors pooled across paths,
      windows never cross path boundaries) vs Sturmian n+1 vs the matched
      Beatty pool vs the random control;
  (c) Beatty-language membership: fraction of zero-subwords that are factors
      of the Beatty word (Sturmian languages are reversal-closed, so the
      inverse-graph orientation is irrelevant);
  (d) trap-run structure: maximal pure tau=1 zero-run, and the level profile
      min_dist(j) (where the -1-per-level trap bends, the corridor bound must
      take over).

Honest scope: certified slices are SHALLOW (j <= Q <= 8), so "asymptotically
Sturmian" can only be probed through factor statistics at n <= ~8 and through
the bend of min_dist(j); the verdict is about whether the Beatty dictionary
is even the right local language, not a limit theorem.

Usage:  python sturmian_gate.py [Q ...]    (default: 3 5 8)
"""
from __future__ import annotations
import sys, json, math, time, random
from collections import defaultdict, Counter
from decimal import Decimal, getcontext

sys.path.insert(0, r"C:\Users\benet\Downloads\collatz-admissible-tree\tools")
from kappa_precise_probe import KappaEngine
from s202_engine import State, a202_mod, TAU, W202
from phi_quotient_refuter import backward_region

getcontext().prec = 60
LOG23 = Decimal(3).ln() / Decimal(2).ln()      # log2(3), 60 digits
GAMMA = float(LOG23)
POW3 = [3 ** i for i in range(80)]


# --------------------------------------------------------------------------
# Beatty / continued-fraction reference machinery
# --------------------------------------------------------------------------
def beatty_word(n: int):
    """b_i = floor((i+1)*g) - floor(i*g), i=1..n, g=log2(3); symbols {1,2}."""
    g = LOG23
    out = []
    prev = int(g)            # floor(1*g) with i starting at 1
    for i in range(2, n + 2):
        cur = int(i * g)
        out.append(cur - prev)
        prev = cur
    return out


def contfrac_log23(k: int = 14):
    x = LOG23
    terms = []
    for _ in range(k):
        a = int(x)
        terms.append(a)
        fr = x - a
        if fr == 0:
            break
        x = 1 / fr
    # convergents
    conv = []
    h0, h1, k0, k1 = 0, 1, 1, 0
    for a in terms:
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        conv.append((h1, k1))
    return terms, conv


def factor_set(words, n: int):
    """Distinct length-n factors pooled over a list of words (within-word)."""
    s = set()
    for w in words:
        for i in range(len(w) - n + 1):
            s.add(tuple(w[i:i + n]))
    return s


def complexity_table(words, nmax: int = 8):
    return {n: len(factor_set(words, n)) for n in range(1, nmax + 1)
            if any(len(w) >= n for w in words)}


# --------------------------------------------------------------------------
# path families
# --------------------------------------------------------------------------
def best_table(m, Q, T_hi, max_states):
    for T in range(T_hi, 0, -1):
        eng = KappaEngine(m=m, Q=Q, threshold=T)
        res = eng.search_or_certify_bf(max_states=max_states)
        if res["status"] == "barrier_certificate":
            return T, eng, res["states"]
    return None, None, None


def preds(R, j, c):
    """The exactly-two in-neighbors of (j,c): ((j',c'), kappa, tau, bit)."""
    M = POW3[R + j]
    t = TAU[c % 9]
    v = (pow(2, t, M) * c) % M
    out = [((j, v), 1, t, 1)]
    if j >= 1:
        out.append(((j - 1, (v - 1) // 3), -1 if t == 1 else 0, t, 0))
    return out


def reconstruct(dist, R, start_key, target, prefer_zero=True):
    """One argmin path start->target as a word [(bit, tau, kappa), ...]."""
    path = []
    cur, dc = target, dist[target]
    for _ in range(10000):
        if cur == start_key:
            path.reverse()
            return path
        opts = [o for o in preds(R, *cur)
                if dist.get(o[0]) is not None and dist[o[0]] + o[1] == dc]
        if not opts:
            return None
        opts.sort(key=lambda o: o[3] != (0 if prefer_zero else 1))
        p, k, t, bit = opts[0]
        path.append((bit, t, k))
        cur, dc = p, dist[p]
    return None


def forward_paths(m, Q, T_hi=5, max_states=4_000_000, n_targets=2500, seed=2422):
    T, eng, fstates = best_table(m, Q, T_hi, max_states)
    if T is None:
        return None
    R = eng.R
    dist = {(s["j"], s["c"]): s["dist"] for s in fstates}
    start_key = (0, a202_mod(R))
    # level profile of min dist + width of the floor corridor
    min_by_j = {}
    for (j, c), d in dist.items():
        if j not in min_by_j or d < min_by_j[j]:
            min_by_j[j] = d
    width_by_j = Counter()
    for (j, c), d in dist.items():
        if d == min_by_j[j]:
            width_by_j[j] += 1
    # targets: per level the cheapest states + the global optimistic frontier
    rng = random.Random(seed)
    by_j = defaultdict(list)
    for (j, c), d in dist.items():
        by_j[j].append((d, c))
    targets = []
    for j in sorted(by_j):
        if j == 0:
            continue
        lst = sorted(by_j[j])[: max(50, n_targets // (2 * max(Q, 1)))]
        targets += [(j, c) for (_, c) in lst]
    opt = min(d - (Q - j) for (j, c), d in dist.items())
    front = [(j, c) for (j, c), d in dist.items() if d - (Q - j) == opt]
    if len(front) > n_targets:
        front = rng.sample(front, n_targets)
    targets = list(dict.fromkeys(targets + front))
    paths = []
    for pz in (True, False):
        for tgt in targets:
            p = reconstruct(dist, R, start_key, tgt, prefer_zero=pz)
            if p:
                paths.append(tuple(p))
    paths = list(dict.fromkeys(paths))
    return {"T": T, "eng": eng, "R": R, "dist": dist, "paths": paths,
            "min_by_j": min_by_j, "width_by_j": dict(width_by_j),
            "n_targets": len(targets)}


def backward_paths(m, Q, R, eng, cap=6, seed=2423):
    psi, _ = backward_region(m, Q, R, cap=cap, max_states=600_000)
    paths = []
    for pz in (True, False):
        for (j, c), p in psi.items():
            if c == 1:
                continue
            word = []
            cur, pc = (j, c), p
            ok = False
            for _ in range(10000):
                if cur[1] == 1:
                    ok = True
                    break
                opts = []
                for (tgt, w) in eng.outgoing_edges(State(*cur)):
                    key = (tgt.j, tgt.c)
                    pv = psi.get(key)
                    if pv is not None and pv == pc - w:
                        bit = 1 if tgt.j == cur[0] else 0
                        opts.append((key, w, TAU[tgt.c % 9], bit))
                if not opts:
                    break
                opts.sort(key=lambda o: o[3] != (0 if pz else 1))
                key, w, t, bit = opts[0]
                word.append((bit, t, w))
                cur, pc = key, pc - w
            if ok and word:
                paths.append(tuple(word))
    return list(dict.fromkeys(paths)), psi


def random_walks(eng, Q, n_walks=3000, seed=2424):
    rng = random.Random(seed)
    R = eng.R
    start = State(0, a202_mod(R))
    paths = []
    for _ in range(n_walks):
        cur = start
        word = []
        for _ in range(400):
            if cur.j >= Q:
                break
            es = eng.outgoing_edges(cur)
            if not es:
                break
            tgt, w = rng.choice(es)
            bit = 1 if tgt.j == cur.j else 0
            word.append((bit, TAU[tgt.c % 9], w))
            cur = tgt
        if word:
            paths.append(tuple(word))
    return paths


def attractor_note(R=24, trials=4000, jmax=12, seed=2426):
    """The two 3-adic attractor laws that EXPLAIN both gates' headline data.
    Verified here property-based AND against the real engine edges; each is a
    2-line LTE-style identity (prime Lean targets):

      (A-)  tau=1 zero-edge  y = (3c+1)/2 :   y+1 = 3(c+1)/2, so
            nu3(y+1) = nu3(c+1) + 1;  once nu3(c+1) >= 2 the class is 8 mod 9
            (tau=1, kappa=-1) FOREVER  =>  the kappa=-1 trap filament never
            dies, min_dist(j) = -j, width 1 (slope -1, NOT Beatty).

      (A+)  tau=2 zero-edge  y = (3c+1)/4 :   y-1 = 3(c-1)/4, so
            nu3(y-1) = nu3(c-1) + 1;  once nu3(c-1) >= 2 the class is 1 mod 9
            (tau=2, kappa=0) FOREVER  =>  from aS202 (nu3(aS202-1) = 22 = R-2,
            because the W202 cylinder contains n=1) the kappa-cost-0 chain
            realizes nu3(c_j - 1) = 22 + j: the depth profile that refutes the
            real-valued Hoelder corrector in GATE A at t = R+Q-2 for EVERY Q."""
    rng = random.Random(seed)
    ok_minus = ok_plus = True
    for _ in range(trials):
        k = rng.randrange(4, 30)
        M = POW3[k]
        v = rng.randrange(0, k - 2)
        c = (rng.randrange(1, POW3[k - v]) * POW3[v] - 1) % M    # nu3(c+1)>=v
        if (c + 1) % POW3[v] != 0:
            continue
        vv = 0
        x = (c + 1) % M
        while x % 3 == 0 and x:
            x //= 3
            vv += 1
        y = ((3 * c + 1) * pow(2, -1, 3 * M)) % (3 * M)
        w = 0
        x = (y + 1) % (3 * M)
        while x % 3 == 0 and x:
            x //= 3
            w += 1
        if (c + 1) % M and (y + 1) % (3 * M) and w != vv + 1:
            ok_minus = False
        cp = (c + 2) % M                                          # nu3(cp-1)>=v
        y = ((3 * cp + 1) * pow(4, -1, 3 * M)) % (3 * M)
        vv = 0
        x = (cp - 1) % M
        while x and x % 3 == 0:
            x //= 3
            vv += 1
        w = 0
        x = (y - 1) % (3 * M)
        while x and x % 3 == 0:
            x //= 3
            w += 1
        if (cp - 1) % M and (y - 1) % (3 * M) and w != vv + 1:
            ok_plus = False
    print(f"ATTRACTOR LAWS (property check, {trials} random instances): "
          f"(A-) nu3(y+1)=nu3(c+1)+1: {'OK' if ok_minus else 'FAIL'};  "
          f"(A+) nu3(y-1)=nu3(c-1)+1: {'OK' if ok_plus else 'FAIL'}")
    # engine-verified chains from aS202 (real kappa-precise edges, R=24)
    from kappa_precise_probe import KappaEngine
    eng = KappaEngine(m=1, Q=jmax, threshold=1)
    c = a202_mod(R)
    cm, cp = c, c
    prof_minus, prof_plus = [], []
    for j in range(jmax):
        nxt_m = nxt_p = None
        for (tgt, w) in eng.outgoing_edges(State(j, cm)):
            if tgt.j == j + 1 and w == -1:
                nxt_m = tgt.c
        for (tgt, w) in eng.outgoing_edges(State(j, cp)):
            if tgt.j == j + 1 and w == 0 and (tgt.c - 1) % 9 == 0:
                nxt_p = tgt.c
        if nxt_m is None or nxt_p is None:
            prof_minus.append(None if nxt_m is None else 0)
            break
        cm, cp = nxt_m, nxt_p
        x, t = cp - 1, 0
        while x % 3 == 0 and x:
            x //= 3
            t += 1
        prof_minus.append(-(j + 1))
        prof_plus.append(t)
    print(f"  engine-verified: kappa=-1 filament reaches dist -j for j=1.."
          f"{len(prof_minus)} from aS202; kappa=0 goal-shadow chain has "
          f"nu3(c_j - 1) = {prof_plus} (law predicts 22+j)")
    print(f"  => GATE A break extends to every Q: pair (chain state at j=Q) ~ "
          f"goal (j,1) agrees mod 3^(22+Q); L*(alpha) = m * 3^((22+Q)*alpha), "
          f"e.g. Q=8: t=30.")
    return {"law_minus_ok": ok_minus, "law_plus_ok": ok_plus,
            "nu3_chain": prof_plus}


def w202_word():
    """tau-sequence of the actual S202 witness word (evalWord from n=1)."""
    n = 1
    seq = []
    for ch in W202:
        t = TAU[n % 9]
        bit = 1 if ch == "1" else 0
        seq.append((bit, t, (1 if bit else (-1 if t == 1 else 0))))
        n = (2 ** t) * n if bit else ((2 ** t) * n - 1) // 3
    return seq


# --------------------------------------------------------------------------
# statistics per family
# --------------------------------------------------------------------------
def run_stats(name, paths, beatty_factors, nmax=8):
    if not paths:
        print(f"  {name}: NO paths")
        return None
    full = [[t for (b, t, k) in p] for p in paths]
    zsub = [[t for (b, t, k) in p if b == 0] for p in paths]
    zsub = [w for w in zsub if w]
    bits = [[b for (b, t, k) in p] for p in paths]
    ks = Counter(k for p in paths for (b, t, k) in p)
    tauf = Counter(t for w in full for t in w)
    tauz = Counter(t for w in zsub for t in w)
    ne = sum(tauf.values())
    nz = sum(tauz.values())
    zfrac = sum(1 for w in bits for b in w if b == 0) / max(ne, 1)
    mean_tz = sum(t * c for t, c in tauz.items()) / max(nz, 1)
    lens = sorted(len(p) for p in paths)
    print(f"  {name}: {len(paths)} paths, {ne} edges, len p5/50/95 = "
          f"{lens[len(lens)//20]}/{lens[len(lens)//2]}/{lens[-max(1,len(lens)//20)]}")
    print(f"    kappa-type freq: " + ", ".join(
        f"{k:+d}:{v/ne:.3f}" for k, v in sorted(ks.items())))
    print(f"    tau freq FULL: " + ", ".join(
        f"{t}:{v/ne:.3f}" for t, v in sorted(tauf.items())) +
        f"   | zero-frac={zfrac:.3f}")
    print(f"    tau freq ZERO-EDGES: " + ", ".join(
        f"{t}:{v/max(nz,1):.3f}" for t, v in sorted(tauz.items())) +
        f"   mean tau_z = {mean_tz:.4f}  (Beatty(log2 3) predicts "
        f"freq(2)={GAMMA-1:.3f}, mean={GAMMA:.4f})")
    # factor complexity
    cz = complexity_table(zsub, nmax)
    cf = complexity_table(full, nmax)
    print(f"    complexity p(n), zero-subwords: " +
          ", ".join(f"{n}:{c}" for n, c in cz.items()) + "   [Sturmian: n+1]")
    print(f"    complexity p(n), full tau-words: " +
          ", ".join(f"{n}:{c}" for n, c in cf.items()))
    # Beatty membership of zero-subwords (whole subword as a factor)
    member = nonbin = 0
    for w in zsub:
        if any(t > 2 for t in w):
            nonbin += 1
        elif tuple(w) in beatty_factors.get(len(w), set()) or \
                (len(w) > max(beatty_factors) if beatty_factors else False):
            member += 1
    nzw = len(zsub)
    print(f"    Beatty-language membership of zero-subwords: "
          f"{member}/{nzw} = {member/max(nzw,1):.3f}   "
          f"(contain tau>=3: {nonbin}/{nzw} = {nonbin/max(nzw,1):.3f})")
    # runs of tau=1 on zero edges
    mx = 0
    for w in zsub:
        run = best = 0
        for t in w:
            run = run + 1 if t == 1 else 0
            best = max(best, run)
        mx = max(mx, best)
    print(f"    longest pure tau=1 zero-run: {mx}")
    return {"n_paths": len(paths), "n_edges": ne,
            "kappa_freq": {str(k): v / ne for k, v in ks.items()},
            "tau_full": {str(t): v / ne for t, v in tauf.items()},
            "tau_zero": {str(t): v / max(nz, 1) for t, v in tauz.items()},
            "mean_tau_zero": mean_tz, "zero_frac": zfrac,
            "complexity_zero": cz, "complexity_full": cf,
            "beatty_member_frac": member / max(nzw, 1),
            "nonbinary_frac": nonbin / max(nzw, 1),
            "max_tau1_run": mx}


def matched_beatty_pool(lengths, B, seed=2425):
    """Chop the Beatty word into random segments matching `lengths`."""
    rng = random.Random(seed)
    out = []
    for ln in lengths:
        if ln >= len(B):
            continue
        i = rng.randrange(0, len(B) - ln)
        out.append(tuple(B[i:i + ln]))
    return out


# --------------------------------------------------------------------------
def run(m, Q, max_states=4_000_000, cap=6, nmax=8):
    print(f"=== GATE B: Sturmian structure  m={m} Q={Q} ===", flush=True)
    t0 = time.time()
    fw = forward_paths(m, Q, max_states=max_states)
    if fw is None:
        print(f"  no certified table for Q={Q} within budget — skip")
        return None
    print(f"  table: T={fw['T']}, {len(fw['dist'])} states "
          f"[{time.time()-t0:.0f}s]; {len(fw['paths'])} distinct forward "
          f"optimal paths from {fw['n_targets']} targets")
    prof = ", ".join(f"j{j}:{d}" for j, d in sorted(fw["min_by_j"].items()))
    wid = ", ".join(f"j{j}:{fw['width_by_j'].get(j, 0)}"
                    for j in sorted(fw["min_by_j"]))
    print(f"  LEVEL PROFILE min_dist(j): {prof}")
    print(f"    floor width (#states at min): {wid}")
    print(f"    (-j = absolute floor = pure tau=1 trap; a Beatty(log2 3) "
          f"zero-word would give ~(log2(3)-2)*j = {GAMMA-2:.3f}*j)")

    bw, psi = backward_paths(m, Q, fw["R"], fw["eng"], cap=cap)
    print(f"  backward cone: {len(psi)} states -> {len(bw)} distinct "
          f"psi-optimal chains")
    ctrl = random_walks(fw["eng"], Q)

    # Beatty reference: factors by length, up to the longest zero-subword
    B = beatty_word(120_000)
    maxlen = 0
    for fam in (fw["paths"], bw):
        for p in fam:
            maxlen = max(maxlen, sum(1 for (b, t, k) in p if b == 0))
    beatty_factors = {n: factor_set([B], n) for n in range(1, maxlen + 1)}

    out = {"Q": Q, "T": fw["T"], "min_by_j": fw["min_by_j"],
           "width_by_j": fw["width_by_j"]}
    out["forward"] = run_stats("FORWARD optimal (start->frontier)",
                               fw["paths"], beatty_factors, nmax)
    out["backward"] = run_stats("BACKWARD optimal (cone->goal)",
                                bw, beatty_factors, nmax)
    out["control"] = run_stats("CONTROL random admissible walks",
                               ctrl, beatty_factors, nmax)
    # matched Beatty pool (compare complexity fairly)
    zlens = [sum(1 for (b, t, k) in p if b == 0) for p in fw["paths"]]
    bp = matched_beatty_pool([l for l in zlens if l > 0], B)
    cb = complexity_table([list(w) for w in bp], nmax)
    print(f"  matched Beatty pool ({len(bp)} segments): complexity " +
          ", ".join(f"{n}:{c}" for n, c in cb.items()))
    out["beatty_matched_complexity"] = cb
    print(flush=True)
    return out


if __name__ == "__main__":
    qs = [int(a) for a in sys.argv[1:]] or [3, 5, 8]
    terms, conv = contfrac_log23()
    print(f"log2(3) = {GAMMA:.12f} = [{terms[0]};{','.join(map(str, terms[1:]))}]")
    print("  convergents: " + ", ".join(f"{p}/{q}" for p, q in conv))
    w = w202_word()
    zs = [t for (b, t, k) in w if b == 0]
    print(f"W202 reference word: tau-seq = {[t for (_, t, _) in w]}")
    print(f"  zero-edge tau-subword ({len(zs)} symbols): {zs}")
    B = beatty_word(2000)
    fac = factor_set([B], len(zs))
    print(f"  W202 zero-subword in Beatty language: {tuple(zs) in fac}  "
          f"(mean tau_z = {sum(zs)/len(zs):.4f} vs log2(3) = {GAMMA:.4f})")
    note = attractor_note()
    print()
    res = {"contfrac": terms, "convergents": conv,
           "w202_tau": [t for (_, t, _) in w], "w202_zero_tau": zs,
           "attractor_laws": note}
    for Q in qs:
        r = run(1, Q)
        if r:
            res[str(Q)] = r
    path = r"C:\Users\benet\Downloads\collatz-admissible-tree\tools\sturmian_gate_data.json"
    with open(path, "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1, default=str)
    print(f"[data tables written to {path}]")
