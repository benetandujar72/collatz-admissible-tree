/-
S240 — Phase 1 of the reachability verdict: the canonical-first-split DEVICE is refutable.

The S240 reachability workflow showed (strong-sketch) that the trap cylinder dlog=2 / c≡4 is
REACHABLE from InvStart(m+1) via an explicit one-edge ladder, with the goal as the FIRST
m-precise vertex — so `FirstMPrecisionSuffixPositive` fails through the degenerate empty-suffix
channel (mid = goal, vs₂ = [], κ₂ = 0).  THE BARRIER ITSELF SURVIVES (it is existential over the
split); only this particular reduction device dies.

This module formalizes the SOLID, reusable brick of that refutation — the "shield":

  * `ladder_vertex_not_mPrecise` — any vertex whose c-residue is ≡ 4 or 7 (mod 9) is NOT
    m-precise.  (Much simpler than the synthesis's `dlog_reduce`/mod-6 argument: m-precision
    forces c ≡ 1 mod 3^(22m+2+j), hence c ≡ 1 mod 9, contradicting c ≡ 4 or 7.)  Combined with
    `oneEdge_source_mod9_in_four_seven` (S240 N2), every one-edge source on the ladder is shielded.

The remaining piece of the negative theorem — the EXISTENCE of the (astronomical, ~10²¹-edge)
one-edge ladder WPath, by induction on the dlog value (NOT enumeration) — is the genuine hard
plumbing and is tracked as the next target.

Pure mod-9 arithmetic for the shield; axioms {propext, Quot.sound}.  Builds narrow.
-/

import CollatzLean4.BlockBoundaryWork
import CollatzLean4.OneEdgeMod9

namespace CollatzLean4.Admissible

/-- **The shield.**  A vertex whose c-residue is `≡ 4` or `≡ 7 (mod 9)` is NOT `m`-precise.
Reason: `projMPrecise m v` unfolds to `v.c ≡ 1 (mod 3^(22m+2+v.j))`, and since
`9 = 3^2 ∣ 3^(22m+2+v.j)` this forces `v.c ≡ 1 (mod 9)`, contradicting `v.c ∈ {4,7} (mod 9)`.
So every ladder vertex (one-edge source, `≡ 4/7 mod 9` by S240 N2) is automatically non-precise —
the goal is the first `m`-precise vertex on the trap-reaching path. -/
theorem ladder_vertex_not_mPrecise {m : Nat} {v : InvVertex}
    (hc : v.c % 9 = 4 ∨ v.c % 9 = 7) :
    ¬ projMPrecise m v := by
  unfold projMPrecise InvVertex.IsGoal
  simp only [projπ_j, projπ_c]
  intro h
  have hN1 : (1 : Nat) < 3 ^ (22 * m + 2 + v.j) := by
    have h3 : (3 : Nat) ^ 1 ≤ 3 ^ (22 * m + 2 + v.j) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [pow_one] at h3; omega
  have hNdvd : (9 : Nat) ∣ 3 ^ (22 * m + 2 + v.j) := by
    have h9 : (9 : Nat) = 3 ^ 2 := by norm_num
    rw [h9]; exact pow_dvd_pow 3 (by omega)
  rw [Nat.mod_mod_of_dvd v.c (dvd_refl _), Nat.mod_eq_of_lt hN1] at h
  have h9 : v.c % 9 = 1 := by
    rw [← Nat.mod_mod_of_dvd v.c hNdvd, h]
  rcases hc with h4 | h7 <;> omega

/-- The shield, specialized to a one-edge source via S240 N2: the SOURCE of any inverse
one-edge is never `m`-precise. -/
theorem oneEdge_source_not_mPrecise {m R : Nat} (hR : 2 ≤ R) {v v' : InvVertex} {ω : Int}
    (he : InvEdgeOne R v v' ω) :
    ¬ projMPrecise m v :=
  ladder_vertex_not_mPrecise (oneEdge_source_mod9_in_four_seven hR he)

end CollatzLean4.Admissible
