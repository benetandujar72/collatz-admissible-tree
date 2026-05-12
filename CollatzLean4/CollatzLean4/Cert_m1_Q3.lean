/-
Concrete barrier certificate (Python-generated): m = 1, Q = 3, T = 1.

Auto-derived from the external `S202Engine` backward DFS over the
inverse cylinder graph. The 22 visited states cover the entire
"cheap region" (cost < 1) reachable from `InvStart 1` within
at most 3 inverse zero-steps.

DECIDABLE CHECK: `closure_check_m1_Q3 = true` (verified by
`native_decide` below) certifies that for every visited state `s`
with dist `ds`, every outgoing inverse-edge `(s, v, ω)` satisfies
`lookup_m1_Q3 v ≤ ds + ω`. Since `1` is the sentinel for unvisited
vertices and the cost threshold is `1`, this is exactly the
Bellman-Ford relaxation invariant.

EMPIRICAL CONCLUSION: no admissible word `u` with `q(u) ≤ 3` and
`n(u) ≡ aS202 (mod 3^24)` has defect `D(u) < 1`. Equivalently:
`𝒞^←_{S202}(1, 3) ≥ 1`.

NOT proven here: the implication from `closure_check_m1_Q3 = true`
to the formal barrier theorem. That requires the path-induction
lemma (next module in the pipeline, deferred for soundness).
-/

import CollatzLean4.InverseGraph

namespace CollatzLean4.Admissible.Certificates

open CollatzLean4.Admissible

/-- The 22 visited states of the certificate, each with its dist value.
Sorted by (j, c) for readability. -/
def Cert_m1_Q3 : List (InvVertex × Int) :=
  [ (⟨0, 31381059610⟩,    0)
  , (⟨1, 470715894137⟩,  -1)
  , (⟨1, 659002251790⟩,   0)
  , (⟨2, 353036920603⟩,  -1)
  , (⟨2, 706073841206⟩,  -2)
  , (⟨2, 1129718145925⟩,  0)
  , (⟨2, 1447451374466⟩,  0)
  , (⟨2, 2259436291850⟩, -1)
  , (⟨3, 529555380905⟩,  -2)
  , (⟨3, 847288609444⟩,   0)
  , (⟨3, 1694577218888⟩, -1)
  , (⟨3, 2038788216473⟩,  0)
  , (⟨3, 3468587744908⟩,  0)
  , (⟨3, 3706887666314⟩,  0)
  , (⟨3, 4077576432946⟩, -1)
  , (⟨3, 4871909504303⟩, -3)
  , (⟨3, 5983975804193⟩, -1)
  , (⟨3, 6248753494645⟩, -2)
  , (⟨3, 6804786644590⟩,  0)
  , (⟨3, 6937175489816⟩, -1)
  , (⟨3, 7201953180269⟩, -2)
  , (⟨3, 7413775332628⟩, -1) ]

/-- Lookup with sentinel `T = 1` for unvisited vertices. -/
def lookup_m1_Q3 (v : InvVertex) : Int :=
  ((Cert_m1_Q3.find? (·.1 = v)).map (·.2)).getD 1

/-- Closure invariant check: for every visited `(s, ds)`, every outgoing
inverse-edge `(s, v, ω)` (using budget `Q=3`) has
`lookup_m1_Q3 v ≤ ds + ω`. Decidable. -/
def closure_check_m1_Q3 : Bool :=
  Cert_m1_Q3.all (fun ⟨s, ds⟩ =>
    (outgoingEdges 24 3 s).all (fun (e : InvVertex × Int) =>
      decide (lookup_m1_Q3 e.1 ≤ ds + e.2)))

/-- **Empirical closure verification**: the dist table satisfies the
Bellman-Ford relaxation invariant for all generated edges. Verified
by `native_decide`. -/
theorem closure_holds_m1_Q3 : closure_check_m1_Q3 = true := by
  native_decide

/-- No-goal-in-cheap-region check: no visited vertex with `dist < 1`
is a goal (i.e., has `c % 3^(24+v.j) = 1` at its own cylinder modulus). -/
def no_goal_check_m1_Q3 : Bool :=
  Cert_m1_Q3.all (fun (p : InvVertex × Int) =>
    let v := p.1; let d := p.2
    !decide (d < (1 : Int)) ||
    !decide (v.c % (3 ^ (24 + v.j)) = 1 % (3 ^ (24 + v.j))))

theorem no_goal_holds_m1_Q3 : no_goal_check_m1_Q3 = true := by
  native_decide

/-- The starting vertex has dist `0` ≤ threshold. -/
theorem start_dist_m1_Q3 : lookup_m1_Q3 (InvStart 1) = 0 := by
  native_decide

end CollatzLean4.Admissible.Certificates
