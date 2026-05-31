/-
S240 — Mod-9 structure of inverse one-edges: the deep-jump uniqueness lemma.

New forward mathematics from the S240 κ-sign research round (verified against sources).
Along an admissible one-edge `v → v'` the consistency clause forces
`v.c ≡ 2^τ(v'.c) · v'.c (mod 3^(R+j))`, hence mod 9.  Two consequences:

  * the SOURCE residue `v.c % 9` is always `4` or `7` (`oneEdge_source_mod9_in_four_seven`);
  * the source is `≡ 2^τ (mod 9)` — equivalently `9 ∣ (v.c − 2^τ)`, i.e. the 3-adic jump
    `ν₃(v.c − 2^τ) ≥ 2` — IFF the target residue `α = v'.c % 9` equals `1`
    (`oneEdge_deepjump_iff`), in which case `τ = τ(1) = 2` and `v.c ≡ 4 (mod 9)`
    (`dlog = 2`) (`oneEdge_deepjump_source_four`).

So the UNIQUE admissible one-edge that can lift `ρ₊` across a gap `≥ 2` (a fortiori the
final 22-digit precision gap) is the `τ = 2 / α = 1` edge, whose source sits in the single
residue cylinder `dlog = 2 / c ≡ 4`.  This collapses the project's prose "computationally
invisible depth-3²¹ trap" to one explicitly named cylinder.

Pure mod-9 arithmetic; no `native_decide`, no Q10 certificate.  Builds narrow.
-/

import CollatzLean4.InverseGraph

namespace CollatzLean4.Admissible

/-- **One-edge consistency, reduced mod 9.**  From `v.c ≡ 2^τ(v'.c)·v'.c (mod 3^(R+j))`
(with `2 ≤ R`, so `9 = 3^2 ∣ 3^(R+j)`) we get `v.c ≡ 2^τ(v'.c)·v'.c (mod 9)`. -/
theorem oneEdge_vc_mod9 {R : Nat} (hR : 2 ≤ R) {v v' : InvVertex} {ω : Int}
    (he : InvEdgeOne R v v' ω) :
    v.c % 9 = (2 ^ tau v'.c * v'.c) % 9 := by
  obtain ⟨hj, hX', hcong, hτ⟩ := he
  have hme : v.c ≡ 2 ^ tau v'.c * v'.c [MOD 3 ^ (R + v.j)] := hcong
  have hdvd : (3 : Nat) ^ 2 ∣ 3 ^ (R + v.j) := pow_dvd_pow 3 (by omega)
  exact hme.of_dvd hdvd

/-- **Every inverse one-edge SOURCE is ≡ 4 or 7 (mod 9).**  New S240 structural fact.
Since `InvStart`'s residue is `aS202 ≡ 1 (mod 9)`, the start has no one-edge out, and the
one-edge orbit lives entirely in the `{4, 7}` mod-9 classes. -/
theorem oneEdge_source_mod9_in_four_seven {R : Nat} (hR : 2 ≤ R) {v v' : InvVertex} {ω : Int}
    (he : InvEdgeOne R v v' ω) :
    v.c % 9 = 4 ∨ v.c % 9 = 7 := by
  have hmod9 := oneEdge_vc_mod9 hR he
  obtain ⟨hj, hX', hcong, hτ⟩ := he
  rw [hmod9, Nat.mul_mod]
  rcases hX' with h | h | h | h | h | h <;> simp only [tau, h] <;> decide

/-- **The deep-jump uniqueness lemma (mod-9 core).**  The one-edge source satisfies
`v.c ≡ 2^τ(v'.c) (mod 9)` — equivalently `9 ∣ (v.c − 2^τ)`, i.e. the 3-adic jump
`ν₃(v.c − 2^τ) ≥ 2` — IF AND ONLY IF the target residue `v'.c % 9 = 1`.  This is the only
admissible one-edge that can lift `ρ₊` across a gap `≥ 2`. -/
theorem oneEdge_deepjump_iff {R : Nat} (hR : 2 ≤ R) {v v' : InvVertex} {ω : Int}
    (he : InvEdgeOne R v v' ω) :
    v.c ≡ 2 ^ tau v'.c [MOD 9] ↔ v'.c % 9 = 1 := by
  have hmod9 := oneEdge_vc_mod9 hR he
  obtain ⟨hj, hX', hcong, hτ⟩ := he
  unfold Nat.ModEq
  rw [hmod9, Nat.mul_mod]
  rcases hX' with h | h | h | h | h | h <;> simp only [tau, h] <;> decide

/-- In the unique deep-jump case (`v'.c % 9 = 1`) the source residue is exactly `4`
(`dlog = 2`) and the weight is `τ = 2`. -/
theorem oneEdge_deepjump_source_four {R : Nat} (hR : 2 ≤ R) {v v' : InvVertex} {ω : Int}
    (he : InvEdgeOne R v v' ω) (hα : v'.c % 9 = 1) :
    v.c % 9 = 4 ∧ tau v'.c = 2 := by
  have hmod9 := oneEdge_vc_mod9 hR he
  refine ⟨?_, ?_⟩
  · rw [hmod9, Nat.mul_mod]
    simp only [tau, hα]
    decide
  · simp only [tau, hα]

end CollatzLean4.Admissible
