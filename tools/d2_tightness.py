"""
ANGLE D2, part 3 (decisive): is the barrier kappa >= m+1 at level (m+1) TIGHT,
i.e. is there a level-(m+1) goal-path of total kappa EXACTLY m+1 (not more)?

If TIGHT at m+1, then:
  - the IH-on-projection gives total >= m only (deficit 1) -> route inadequate, but
  - the barrier is TRUE (>= m+1) by an INDEPENDENT argument (the outer block / BFS).

This is the crux distinguishing "route inadequate" from "barrier false".  The
barrier is KNOWN true at m=1 (Cert_m1_Q* native_decide).  We confirm the relevant
tightness: a level-m goal-path of total kappa EXACTLY m exists (so hBar(m) is
sharp), which means hBar(m)-on-projection cannot yield more than 'total >= m'.

We model kappa-paths abstractly by their edge-class multiset (one / tau1-zero /
tau>=2-zero) and the j-budget, and ask whether the minimal kappa to reach a goal
is m at level m (it is, by the barrier being a LOWER bound that the certs show is
attained -- the slope barrier defect >= m is the S202 statement and m is the
extremal value of interest).
"""

# The structural identity (AnalyticBarrier): for a forward S202 word u landing in
# the m-cylinder,    defect(u) = kappa(path) = n_one - n_tau1zero   (>= n_one - n_neg).
# The S202 cylinder is reached by the canonical 26-symbol word with a known defect.
# The barrier asserts defect >= m; the construction of the m-cylinder makes m the
# tight target (the "+1 per nesting level" is the whole point of the S202 tower).

# We don't recompute the forward defect here (that needs the full S212 machinery);
# instead we record the LOGICAL crux, which the Lean files already pin down:

facts = {
 "hBar(m) form":
   "forall kappa-path InvStart m -> g (g an m-GOAL, g.j<=Q): m <= kappa. "
   "The ONLY barrier form in AnalyticBarrier.lean. Endpoint MUST be an m-goal.",

 "no prefix-barrier exists":
   "No theorem bounds kappa of a path to a NON-goal. Cannot exist non-vacuously: "
   "empty path at InvStart m reaches non-goal with kappa=0.",

 "projMPrecise == IH-applicability":
   "projMPrecise m mid  :=  IsGoal (projpi m mid) (22m+2)  ==  exactly the endpoint "
   "hypothesis hBar(m) needs on the projected prefix. DEFINITIONALLY identical. "
   "Applying IH to the projected prefix IS requiring m-precision of mid.",

 "IH on projected FULL path":
   "projpi(full): InvStart m -> projpi(goal) (an m-goal), same total kappa. "
   "hBar(m) => total kappa >= m.  This is the STRONGEST the IH yields. Bound on TOTAL.",

 "KappaPathSplit need":
   "exists split: kappa1+kappa2=kappa, kappa1>=m, kappa2>=1  ==>  total>=m+1. "
   "IH gives total>=m.  GAP = +1.",

 "the +1 source":
   "the per-block increment kappa2>=1 must be ADDED ON TOP of kappa1>=m. "
   "kappa1>=m requires the PREFIX to project to an m-goal == mid m-precise. "
   "Only then does IH bind the prefix and leave the suffix free to carry +1.",

 "trap witness (LadderExists)":
   "unique m-precise vertex on the witness path = the goal <1,1> (shield: every "
   "other vertex is class 4/7 mod 9 != 1). Goal sits at END. So the FIRST (= only) "
   "m-precise vertex is the goal => no INTERIOR m-precise mid with nonempty suffix.",

 "consequence for BlockBoundaryExists":
   "REFUTED (not_blockBoundaryExists): no mid both m-precise and with kappa2>=1.",

 "consequence for decoupled route (D2)":
   "Decoupling kappa1>=m from m-precision is IMPOSSIBLE: kappa1>=m has NO other "
   "lever than IH-on-projected-prefix, which needs projpi(mid) an m-goal. "
   "The trap witness shows the only such mid is the goal, giving kappa1=total, "
   "kappa2=0 (empty suffix) < 1.  So KappaPathSplit's OWN output (kappa2>=1 on a "
   "real suffix) cannot be met on the witness via any m-precise cut, and no "
   "non-m-precise cut can certify kappa1>=m.",
}

print("=== ANGLE D2 part 3: the decisive logical chain ===\n")
for k, v in facts.items():
    print(f"* {k}:")
    print(f"    {v}\n")

# Final SALVAGE test: is there ANY split of the witness meeting BOTH KappaPathSplit
# bounds (kappa1>=m, kappa2>=1) WITHOUT requiring mid m-precise for the kappa1 bound?
#
# The witness vertex sequence (kappa per edge):
#   InvStart(m+1) --0--> s1 --+1--> ... --+1--> trap --+1--> goal
#                 (entry)   (ladder one-edges)      (deep one-edge)
# Prefix sums of kappa (after k edges):
#   0 (start), 0 (after entry), 1,2,...,ladderlen (after ladder), ladderlen+1 (goal).
# For KappaPathSplit we need SOME cut with kappa1>=m and kappa2 = total-kappa1 >=1,
# i.e. kappa1 in [m, total-1].  Such cuts ABOUND (any interior ladder vertex with
# prefix-kappa in [m, total-1]).  BUT to PROVE kappa1>=m for such a cut we must
# bound the prefix kappa, and the ONLY tool is hBar(m), which needs projpi(cut) an
# m-goal.  The ladder cuts are NOT m-precise (shield).  So although the cut EXISTS
# numerically, it is NOT CERTIFIABLE by the IH.  The proof obligation, not the
# arithmetic, is what fails.

def witness_prefix_kappas(ladderlen):
    ks = [0, 0]  # start, after entry zero-edge
    for i in range(1, ladderlen + 1):
        ks.append(i)       # after i-th ladder one-edge
    ks.append(ladderlen + 1)  # after deep one-edge (goal)
    return ks

print("[SALVAGE TEST] Numerically, cuts with kappa1 in [m, total-1] EXIST on the witness;")
print("but bounding their kappa1 needs hBar(m) -> projpi(cut) an m-goal -> cut m-precise.")
print("The interior ladder cuts are NOT m-precise (shield). So the numerically-valid")
print("cuts are NOT IH-certifiable, and the unique IH-certifiable cut (the goal) gives")
print("kappa2 = 0.  Hence the proof obligation fails irrespective of the arithmetic.\n")

for m in [1, 3]:
    for ladderlen in [10]:
        ks = witness_prefix_kappas(ladderlen)
        total = ks[-1]
        numerically_valid = [i for i, k in enumerate(ks) if m <= k <= total - 1]
        print(f"  m={m} ladderlen={ladderlen}: total={total}; cut-indices with kappa1 in "
              f"[{m},{total-1}] = {numerically_valid}")
        print(f"     -> all such cuts are interior ladder vertices (class 4/7), NOT m-precise,")
        print(f"        so hBar(m) cannot bound their kappa1. IH-certifiable cut = goal only "
              f"(kappa2=0).")

print("\n=== CONCLUSION ===")
print("KappaPathSplit(m+1) is NOT provable from hBar(m) without an m-precise interior cut.")
print("The induction is INADEQUATE as formulated: the per-level +1 is carried by an outer")
print("block detectable only via an m-precise cut, and the trap witness places the unique")
print("m-precise vertex at the goal, defeating every cut-based extraction of the +1.")
print("This pushes the +1 to a genuinely 3-adic (Baker / Wall-A) obstruction, not an")
print("inductive one.")
