/-
S241 — The FAITHFUL per-`m` barrier: Caveat C unlocked for the bit-length potential.

The corpus's `InvStart m = ⟨0, aS202 % 3^(22m+2)⟩` reuses the m=1 representative
`aS202 = 1 + 3²²` (35 bits) at every precision — the long-documented Caveat C: for
`m ≥ 2` it names the WRONG cylinder, and it caps the closed-form potential at
`m + Q ≤ 8`.  `AS202Lift.lean` already carries the faithful representatives
`aS202_at m` (defined by `(2^43 − 3^22)·a ≡ B_{S202} mod 3^(22m+2)`, certified there)
with near-maximal bit lengths: 35, 73, 105 bits for m = 1, 2, 3.

This module plugs the faithful start into the GENERIC-START socket
(`kappa_bounded_barrier_bitlen_from`, BitlenPotential.lean):

  * `InvStartAt m := ⟨0, aS202_at m⟩` — the Caveat-C-corrected start
    (`invStartAt_one`: at m = 1 it coincides with the corpus's `InvStart 1`);
  * `kappa_barrier_at_of_bits` — the bit-criterion wrapper;
  * **`kappa_barrier_at_m2_Q16`** and **`kappa_barrier_at_m3_Q23`** — the faithful
    closed-form barriers at `m = 2` up to `Q = 16` and `m = 3` up to `Q = 23`
    (the bit criterion `4(m+Q)+1 ≤ B₀(m)` is EXACTLY tight at both: 73 = 73, 105 = 105),
    far beyond the `m + Q ≤ 8` cap of the unfaithful start, with no search and no
    certificate tables.

All certificates here are kernel `decide` on the stored literals (no `native_decide`).
Remaining Caveat-C work (documented in AS202Lift): generalising the WORD-level
statements (`S216BarrierForWords`) to `aS202_at`; this module covers the κ-graph side.
-/

import CollatzLean4.AS202Lift
import CollatzLean4.BitlenPotential

namespace CollatzLean4.Admissible

/-- The FAITHFUL start vertex of the m-th S202 cylinder (Caveat-C corrected). -/
def InvStartAt (m : Nat) : InvVertex := ⟨0, aS202_at m⟩

/-- Consistency: at `m = 1` the faithful start coincides with the corpus's `InvStart 1`. -/
theorem invStartAt_one : InvStartAt 1 = InvStart 1 := by decide

/-- The faithful bounded κ-precise barrier (Caveat-C-corrected statement shape):
every κ-precise path from the FAITHFUL m-th start to a goal in the `Q`-slice has
κ-cost at least `m`. -/
def S202_kappa_precise_barrier_bounded_at (m Q : Nat) : Prop :=
  ∀ {goal : InvVertex} {κ : Int} {vs : List InvVertex},
    InvVertex.IsGoal goal (22 * m + 2) → goal.j ≤ Q →
    WPath (InvKappaPreciseEdge (22 * m + 2)) (InvStartAt m) goal κ vs →
    (m : Int) ≤ κ

/-- The bit-criterion wrapper for the faithful start: `4(m+Q)+1 ≤ size(aS202_at m)`
suffices. -/
theorem kappa_barrier_at_of_bits (m Q : Nat)
    (h0 : 4 * (m + Q) + 1 ≤ Nat.size (aS202_at m % 3 ^ (22 * m + 2))) :
    S202_kappa_precise_barrier_bounded_at m Q := by
  intro goal κ vs hg hgQ hpath
  refine kappa_bounded_barrier_bitlen_from m Q (InvStartAt m) ?_ hg hgQ hpath
  show 4 * (m + Q) + 1 ≤ Nat.size (aS202_at m % 3 ^ (22 * m + 2 + 0)) + 4 * 0
  simpa using h0

/-- **The faithful `m = 2` closed-form barrier up to `Q = 16`.**
(`size(aS202_at 2) = 73` and `4·(2+16)+1 = 73` — exactly tight.) -/
theorem kappa_barrier_at_m2_Q16 : S202_kappa_precise_barrier_bounded_at 2 16 := by
  apply kappa_barrier_at_of_bits
  have hlt : aS202_at 2 < 3 ^ (22 * 2 + 2) := by decide
  rw [Nat.mod_eq_of_lt hlt]
  have h72 : (2 : ℕ) ^ 72 ≤ aS202_at 2 := by decide
  have := Nat.lt_size.mpr h72
  omega

/-- **The faithful `m = 3` closed-form barrier up to `Q = 23`.**
(`size(aS202_at 3) = 105` and `4·(3+23)+1 = 105` — exactly tight.) -/
theorem kappa_barrier_at_m3_Q23 : S202_kappa_precise_barrier_bounded_at 3 23 := by
  apply kappa_barrier_at_of_bits
  have hlt : aS202_at 3 < 3 ^ (22 * 3 + 2) := by decide
  rw [Nat.mod_eq_of_lt hlt]
  have h104 : (2 : ℕ) ^ 104 ≤ aS202_at 3 := by decide
  have := Nat.lt_size.mpr h104
  omega

end CollatzLean4.Admissible
