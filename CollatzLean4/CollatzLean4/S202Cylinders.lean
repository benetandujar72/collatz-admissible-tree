/-
S202 Cylinder Accessibility — research front.

Following the strategic re-framing after S202: the rigid auxiliary
conjecture `A ≥ 2q` is FALSE (witnessed by `(43, 22, 919447060349)`),
but the *asymptotic* slope question

      λ_asy := inf_{q→∞} liminf A/q

remains open. The natural target is the accessibility of the
3-adic cylinders around the S202 fixed point:

      AccessibleToS202Cylinder m :≡
        ∃ u : Word, (evalWord u).n ≡ a_S202  (mod 3^{22m+2}).

The "S202 alternative theorem" (stated as a conjecture here, NOT proven):

  Either every cylinder C_m is accessible with controlled defect
  cost `D(u_m) = A(u_m) − 2q(u_m) = o(m)`, in which case
  concatenating `u_m` with m formal S202 blocks yields a symbolic
  family of admissible words with `liminf A/q ≤ 43/22 < 2`
  (subcritical slope); OR accessibility fails infinitely often, in
  which case a new structural 3-adic obstruction governs the
  admissible inverse cover.

CERTIFIED here:
  * Definitions `AccessibleToS202Cylinder` and the bounded-Bool variant
    `reachableModAux` for empirical exploration.
  * `accessible_S202_m0`: cylinder at m = 0 (mod 9) is trivially
    accessible from `initState.n = 1` (since `aS202 % 9 = 1`).
  * `accessible_S202_m1_unreachable_short`: empirical observation that
    no word of length ≤ 8 reaches the m=1 cylinder (mod 3^24) — a small
    quantitative test, NOT a non-accessibility proof.

NOT closed:
  * The S202 alternative theorem itself.
  * Whether `AccessibleToS202Cylinder m` holds for any m ≥ 1.
-/

import CollatzLean4.ThreeAdic

namespace CollatzLean4.Admissible

/-! ### Accessibility predicate -/

/-- Accessibility of the m-th S202 cylinder from `initState`. -/
def AccessibleToS202Cylinder (m : Nat) : Prop :=
  ∃ u : Word,
    (evalWord u).n % (3 ^ (22 * m + 2))
      = aS202 % (3 ^ (22 * m + 2))

/-- Same predicate in `Nat.ModEq` notation. -/
def AccessibleToS202CylinderModEq (m : Nat) : Prop :=
  ∃ u : Word, Nat.ModEq (3 ^ (22 * m + 2)) (evalWord u).n aS202

theorem accessibleToS202Cylinder_iff_modEq (m : Nat) :
    AccessibleToS202Cylinder m ↔ AccessibleToS202CylinderModEq m :=
  Iff.rfl

/-! ### Bounded DFS (empirical exploration tool) -/

/-- DFS up to depth `d`: returns `true` iff some state reachable from `s`
within `d` steps has `s'.n ≡ target (mod modulus)`. -/
def reachableModAux : Nat → Nat → Nat → AdmState → Bool
  | 0,     modulus, target, s => decide (s.n % modulus = target)
  | (d+1), modulus, target, s =>
      decide (s.n % modulus = target) ||
      reachableModAux d modulus target (step s Branch.zero) ||
      reachableModAux d modulus target (step s Branch.one)

/-- Bool helper for `AccessibleToS202Cylinder m`: bounded DFS at depth `d`. -/
def checkS202Accessibility (m d : Nat) : Bool :=
  reachableModAux d (3 ^ (22 * m + 2))
                   (aS202 % (3 ^ (22 * m + 2)))
                   initState

/-! ### S202 cylinder at `m = 0`: trivial accessibility

The m=0 cylinder is `aS202 + 9 · ℤ₃`. We have `aS202 % 9 = 1` and
`initState.n = 1`, so the empty word reaches it. -/

theorem aS202_mod_nine : aS202 % 9 = 1 := S206_a_mod9

theorem accessible_S202_m0 : AccessibleToS202Cylinder 0 := by
  refine ⟨[], ?_⟩
  native_decide

/-- The empty word is a `D = 0` witness for accessibility at m = 0. -/
theorem accessible_S202_m0_defect_zero :
    ∃ u : Word,
      (evalWord u).n % (3 ^ 2) = aS202 % (3 ^ 2) ∧
      (evalWord u).A = 0 ∧ (evalWord u).q = 0 := by
  refine ⟨[], ?_, rfl, rfl⟩
  native_decide

/-! ### Empirical exploration of m = 1 (mod 3^24)

The m=1 cylinder requires `(evalWord u).n ≡ aS202 (mod 3^24)`. Since
`aS202 < 3^24`, this requires `n ≥ aS202 ≈ 3.14 × 10^10`. Such an `n`
is reachable in principle but needs words of substantial length.

Bounded DFS at depth 8 (256 paths) finds NO short witness. This is
empirical data, NOT a proof of non-accessibility. -/

theorem no_short_witness_S202_m1 :
    checkS202Accessibility 1 8 = false := by native_decide

/-! ### Statement of the S202 alternative theorem (NOT proven)

The following is the strategic target stated as a hypothesis whose
proof would represent significant progress on the asymptotic slope
problem. We provide it as a `Prop` so that consequences can be
derived conditionally. -/

/-- Existence of an accessibility family with subcritical defect cost. -/
def SubcriticalAccessFamily : Prop :=
  ∃ u : Nat → Word,
    (∀ m, (evalWord (u m)).n % (3 ^ (22 * m + 2))
            = aS202 % (3 ^ (22 * m + 2))) ∧
    (∀ ε > (0 : Rat),
        ∃ M, ∀ m ≥ M,
          ((evalWord (u m)).A : Rat) - 2 * ((evalWord (u m)).q : Rat)
            ≤ ε * (m : Rat))

/-- Existence of a slope barrier (the alternative). -/
def SlopeBarrier : Prop :=
  ∃ K : Nat, ∀ m ≥ K, ¬ AccessibleToS202Cylinder m

/-- The S202 alternative theorem (CONJECTURE): exactly one of the
above holds. Resolving this is the keystone of the asymptotic slope
program. -/
def S202_alternative_conjecture : Prop :=
  SubcriticalAccessFamily ∨ SlopeBarrier

end CollatzLean4.Admissible
