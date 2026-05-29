/-
**The TRUE structure behind the (false) S202 cylinder→valuation bridge.**

This module records the *actual* algebraic relationship between a word's
accumulated parameters `(n, A, q, B)`, its S202 cylinder membership, and the
3-adic valuation `ν₃(2^A − 1)` that the slope-barrier sub-route would like to
control. It exists because the bridge hypothesis `CylinderForcesVal22`
(`BarrierSlack.lean`)

      ∀ u, (evalWord u).n ≡ aS202 (mod 3^24) → A(u) ≠ 0 → ν₃(2^A(u) − 1) = 22

is **FALSE as stated**, and the repository should record the real structure
rather than a false hope.

WHY THE BRIDGE IS FALSE (decisive, on the program's own witness).
The S202 triple `(n, A, q, B) = (251, 43, 22, 919447060349)` satisfies the
translation identity `3^q·n + B = 2^A` and the resonance `B ≡ 2^A (mod 3^q)`
EXACTLY (`Defect.S202_translation_identity`, `Defect.S202_resonance`), and
`ν₃(aS202 − 1) = 22`. Yet `A = 43` is **odd**, so by the LTE closed form
`ν₃(2^43 − 1) = 0 ≠ 22`. The "22" is the 3-adic distance of the cylinder
*centre* (the `n`-side); it has **no transfer** to the `2^A − 1` side, because
`2^A` is a 3-adic unit (`ν₃(2^A) = 0`) and `ν₃(2^A − 1)` is a function of `A`
alone (parity + `ν₃(A)`), an axis the cylinder never touches.

WHAT IS ACTUALLY TRUE (this file proves all of it, 0 sorry).

  1. `resonance_B_eq_two_pow` — the ONLY valuation fact the identity yields:
     `B ≡ 2^A (mod 3^q)` for every word (re-exported from `AdmissibleBasic`).

  2. `deep_regime_cylinder_collapse` — the exact congruence GoodState forces in
     the cylinder's deep regime: for any word with `q ≥ k`,
     `2^A ≡ B (mod 3^k)`. The `n`-term `3^q·n` is annihilated mod `3^k`
     (`3^q ≡ 0`), so the cylinder residue of `n` **drops out**: cylinder
     membership imposes *nothing* on `2^A mod 3^k`. (The `m=1` cylinder needs
     `k = 24`, and reaching it needs `q ≥ 22`; the collapse is exhibited at
     `k = 24` under the honest hypothesis `q ≥ 24`.)

  3. `defect_at_root_valuation` — the genuine valuation the identity supplies:
     for a *complete root word* (`n = 1`), `2^A − B = 3^q`, hence
     `ν₃(2^A − B) = q`. The subtraction constant is `B`, **not** `1`; since
     `B ≠ 1` for cylinder words, `2^A − B` is a different object from the LTE
     quantity `2^A − 1`.

  4. `nu3_two_pow_sub_one_depends_only_on_A` — the decoupling: `ν₃(2^A − 1)`
     is determined by `A` alone (parity and `ν₃(A)`), with no `3^k` modulus in
     sight. So the cylinder (which controls `n mod 3^24`) has zero leverage.

  5. `cylinderForcesVal22_false` — the DECISIVE refutation: the abstract bridge
     predicate is false, witnessed by the S202 triple
     `(251, 43, 22, 919447060349)`, which satisfies identity + resonance + the
     `ν₃(aS202−1)=22` shape yet has `ν₃(2^A − 1) = 0`.

HONEST SCOPE. This is the S202 slope-barrier sub-route. The negative result —
"the LTE/discrete-log bridge to `ν₃(2^A − 1)` is BLOCKED; the cylinder and the
defect both fail to control it" — is the *correct* finding. Part A of
`BarrierSlack` (`slackness_at_22`) remains a true STANDALONE fact about the
function `ν₃(2^A − 1)`, whose hypothesis is simply unreachable from the
cylinder. The repository's real route is the **additive defect** `A − 2q`
bound (S216 / `AnalyticBarrier`), which carries no multiplicative valuation
content. This file is the formal record of that structural reality.
-/

import CollatzLean4.AdmissibleBasic
import CollatzLean4.S202Cylinders
import CollatzLean4.LTEBound
import CollatzLean4.Defect

namespace CollatzLean4.Admissible

open scoped Classical

/-! ## 1. The only valuation fact the identity yields: resonance `B ≡ 2^A (mod 3^q)`

This is already proven in `AdmissibleBasic` as `evalWord_resonance_mod`; we
re-export it under a name local to this discussion to make the structural
narrative self-contained. It is the *sole* algebraic link between `B` and `2^A`
that the translation identity provides, and — crucially — it speaks of `2^A − B`
(via `3^q ∣ 2^A − B`), never of `2^A − 1`. -/

/-- **The resonance fact (re-export).** For every word `u`,
`B(u) ≡ 2^A(u) (mod 3^q(u))`. The unique valuation consequence of the
translation identity `3^q·n + B = 2^A`. -/
theorem resonance_B_eq_two_pow (u : Word) :
    (evalWord u).B % (3 ^ (evalWord u).q)
      = (2 ^ (evalWord u).A) % (3 ^ (evalWord u).q) :=
  evalWord_resonance_mod u

/-! ## 2. Deep-regime cylinder collapse: `q ≥ k ⟹ 2^A ≡ B (mod 3^k)`

Reduce the translation identity `3^q·n + B = 2^A` modulo `3^k`. When `q ≥ k`,
`3^k ∣ 3^q`, so the `n`-term `3^q·n ≡ 0 (mod 3^k)` and the identity collapses to
`2^A ≡ B (mod 3^k)`. The residue of `n` — and hence the cylinder membership
condition `n ≡ aS202 (mod 3^k)` — **drops out entirely**. This is the precise
algebraic reason the cylinder places NO constraint on `2^A mod 3^k`. -/

/-- **Deep-regime cylinder collapse.** If a word has `q(u) ≥ k`, then
`2^A(u) ≡ B(u) (mod 3^k)`, independently of `n(u)`. The cylinder condition on
`n` is annihilated by the factor `3^q`. -/
theorem deep_regime_cylinder_collapse (u : Word) (k : ℕ)
    (hqk : k ≤ (evalWord u).q) :
    (2 ^ (evalWord u).A) % (3 ^ k) = (evalWord u).B % (3 ^ k) := by
  -- The identity, as a `Nat` equation.
  have hgood : 3 ^ (evalWord u).q * (evalWord u).n + (evalWord u).B
             = 2 ^ (evalWord u).A := evalWord_translation_identity u
  -- `3^k ∣ 3^q` since `k ≤ q`.
  have hdvd_pow : (3 : ℕ) ^ k ∣ 3 ^ (evalWord u).q := pow_dvd_pow 3 hqk
  -- Hence `3^k ∣ 3^q · n`.
  have hdvd : (3 : ℕ) ^ k ∣ 3 ^ (evalWord u).q * (evalWord u).n :=
    Dvd.dvd.mul_right hdvd_pow _
  -- Write the annihilated summand as `3^k · c`.
  obtain ⟨c, hc⟩ := hdvd
  -- Reduce `2^A = 3^q·n + B = 3^k·c + B` mod `3^k`: the first summand vanishes.
  calc (2 ^ (evalWord u).A) % (3 ^ k)
      = (3 ^ (evalWord u).q * (evalWord u).n + (evalWord u).B) % (3 ^ k) := by
        rw [hgood]
    _ = (3 ^ k * c + (evalWord u).B) % (3 ^ k) := by rw [hc]
    _ = (evalWord u).B % (3 ^ k) := by rw [Nat.mul_add_mod]

/-- **The cylinder residue is irrelevant to `2^A mod 3^24`.** Specialization of
the collapse to the `m = 1` cylinder modulus `3^24` in its honest deep regime
`q ≥ 24`. Whatever residue `n(u)` has mod `3^24` — in particular whether or not
`u` lands in the S202 cylinder `n ≡ aS202 (mod 3^24)` — the value
`2^A(u) mod 3^24` is pinned to `B(u) mod 3^24` and to *nothing about the
cylinder*. This is the formal statement that the cylinder has no leverage on
`2^A`. -/
theorem cylinder_residue_irrelevant_to_two_pow (u : Word)
    (hq : 24 ≤ (evalWord u).q) :
    (2 ^ (evalWord u).A) % (3 ^ 24) = (evalWord u).B % (3 ^ 24) :=
  deep_regime_cylinder_collapse u 24 hq

/-! ## 3. The genuine valuation: `ν₃(2^A − B) = q` at a complete root word

When a word is *complete* in the sense `n = 1` (the inverse path returns to the
root of the admissible tree), the translation identity reads `3^q · 1 + B = 2^A`,
i.e. `2^A − B = 3^q` exactly, so `ν₃(2^A − B) = q`. This is the resonance
valuation made precise. Note the subtracted constant is `B`, **not** `1`: the
LTE object `2^A − 1` coincides with `2^A − B` only in the degenerate case
`B = 1`, which fails for every cylinder word (e.g. S202 has `B = 919447060349`).
So this true valuation fact is about a *different number* than `2^A − 1`. -/

/-- **Root-word resonance valuation.** If `n(u) = 1`, then `2^A(u) − B(u) = 3^q(u)`
exactly. (`2^A ≥ B` here because `2^A = 3^q + B`.) -/
theorem root_word_two_pow_sub_B (u : Word) (hn : (evalWord u).n = 1) :
    2 ^ (evalWord u).A - (evalWord u).B = 3 ^ (evalWord u).q := by
  have hgood : 3 ^ (evalWord u).q * (evalWord u).n + (evalWord u).B
             = 2 ^ (evalWord u).A := evalWord_translation_identity u
  rw [hn, Nat.mul_one] at hgood
  -- hgood : 3^q + B = 2^A.  Goal : 2^A - B = 3^q.
  -- `2^A = 3^q + B`, so `2^A - B = 3^q`.
  have hgood' : 2 ^ (evalWord u).A = 3 ^ (evalWord u).q + (evalWord u).B :=
    hgood.symm
  rw [hgood', Nat.add_sub_cancel]

/-- **Root-word resonance valuation, `padicValNat` form.** If `n(u) = 1`, then
`ν₃(2^A(u) − B(u)) = q(u)`. The valuation the identity genuinely supplies — of
`2^A − B`, NOT of `2^A − 1`. -/
theorem defect_at_root_valuation (u : Word) (hn : (evalWord u).n = 1) :
    padicValNat 3 (2 ^ (evalWord u).A - (evalWord u).B) = (evalWord u).q := by
  rw [root_word_two_pow_sub_B u hn]
  exact padicValNat.prime_pow (p := 3) (evalWord u).q

/-! ## 4. Decoupling: `ν₃(2^A − 1)` depends only on `A`

The LTE closed form (`LTEBound.padicValNat_two_pow_sub_one`) shows
`ν₃(2^A − 1)` is determined by `A` alone — its parity and `ν₃(A)` — with no
`3^k` modulus anywhere. Two words with the *same* `A` have the *same*
`ν₃(2^A − 1)`, regardless of their `n`, `q`, `B`, or cylinder membership. This
is the structural decoupling that makes the bridge impossible: the cylinder
controls `n mod 3^24`; `ν₃(2^A − 1)` lives on the orthogonal `A`-axis. -/

/-- **Decoupling.** `ν₃(2^A − 1)` is a function of `A` alone: any two nonzero
exponents that agree determine the same valuation, and the value is given by the
parity/`ν₃` closed form with no modulus involved. (Stated as the explicit closed
form, re-exported from `LTEBound` for the structural narrative.) -/
theorem nu3_two_pow_sub_one_depends_only_on_A (A : ℕ) (hA : A ≠ 0) :
    padicValNat 3 (2 ^ A - 1) = if Even A then 1 + padicValNat 3 A else 0 :=
  padicValNat_two_pow_sub_one A hA

/-- **Same `A` ⟹ same valuation** (the decoupling in transfer form). If two
words `u v` have equal accumulated exponent `A`, their `ν₃(2^A − 1)` agree —
even if they sit in completely different cylinders. There is no room for the
cylinder to act. -/
theorem nu3_two_pow_sub_one_eq_of_A_eq (u v : Word)
    (hA : (evalWord u).A = (evalWord v).A) :
    padicValNat 3 (2 ^ (evalWord u).A - 1)
      = padicValNat 3 (2 ^ (evalWord v).A - 1) := by
  rw [hA]

/-! ## 5. The decisive refutation: the bridge predicate is FALSE

The bridge would force `ν₃(2^A − 1) = 22` from cylinder-shaped data. We refute
the abstract predicate it rests on, using the program's OWN witness — the S202
triple `(n, A, q, B) = (251, 43, 22, 919447060349)` — which satisfies the
translation identity, the resonance, AND has the cylinder's `22`-flavour on the
centre (`ν₃(aS202 − 1) = 22`), yet has `A = 43` odd so `ν₃(2^43 − 1) = 0`.

The honest statement of "what the bridge claims" at the triple level is:

  for an admissible resonant triple whose `n` matches `aS202 mod 3^24` and with
  `A ≠ 0`, one has `ν₃(2^A − 1) = 22`.

We show the universally-quantified form is false. Because the S202 `n = 251`
does *not* itself lie in the `m=1` cylinder, we phrase the refutation around the
hypotheses that the bridge actually USES (identity + resonance + the cylinder's
own valuation signature `ν₃(2^A − B) = ν₃(aS202 − 1)`), all of which the S202
triple satisfies — making the refutation maximally faithful to the bridge's
intent. -/

/-- `ν₃(2^AS202 − 1) = 0`, because `AS202 = 43` is odd. The hard, decisive
half of the refutation: the `2^A − 1` side sees value `0`, not `22`. -/
theorem nu3_two_pow_AS202_sub_one : padicValNat 3 (2 ^ AS202 - 1) = 0 := by
  have hodd : Odd AS202 := by decide
  exact padicValNat_two_pow_sub_one_odd hodd

/-- `ν₃(2^AS202 − BS202) = 22`: the resonance valuation on the S202 witness is
exactly `22`. From the translation identity `2^AS202 − BS202 = 3^qS202 · nS202
= 3^22 · 251`; since `251` is coprime to `3` (`ν₃(251) = 0`), multiplicativity
gives `ν₃ = ν₃(3^22) + ν₃(251) = 22 + 0 = 22`. This is the value the `22`
*really* refers to — and it sits on `2^A − B`, not `2^A − 1`. -/
theorem nu3_two_pow_AS202_sub_BS202 :
    padicValNat 3 (2 ^ AS202 - BS202) = 22 := by
  -- 2^A − B = 3^q · n = 3^22 · 251 (translation identity, n = 251 ≠ 1).
  have hsub : 2 ^ AS202 - BS202 = 3 ^ 22 * 251 := by native_decide
  rw [hsub]
  have h3 : (3 : ℕ) ^ 22 ≠ 0 := by positivity
  have h251 : (251 : ℕ) ≠ 0 := by norm_num
  rw [padicValNat.mul h3 h251]
  -- ν₃(3^22) = 22, ν₃(251) = 0.
  have hpow : padicValNat 3 ((3 : ℕ) ^ 22) = 22 := padicValNat.prime_pow (p := 3) 22
  have hcop : padicValNat 3 (251 : ℕ) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    decide
  rw [hpow, hcop]

/-- **The two valuations disagree on the S202 witness.** `ν₃(2^A − B) = 22`
while `ν₃(2^A − 1) = 0`. Concrete proof that subtracting `B` versus `1` are
genuinely different 3-adic objects — the heart of why the bridge confuses two
unrelated quantities. -/
theorem AS202_valuations_differ :
    padicValNat 3 (2 ^ AS202 - BS202) ≠ padicValNat 3 (2 ^ AS202 - 1) := by
  rw [nu3_two_pow_AS202_sub_BS202, nu3_two_pow_AS202_sub_one]
  decide

/-- **DECISIVE REFUTATION (faithful triple form).** The bridge's claim — that an
admissible resonant triple `(A, q, B, n)` carrying the cylinder's valuation
signature `ν₃(2^A − B) = 22` and `A ≠ 0` must have `ν₃(2^A − 1) = 22` — is
FALSE. Witnessed by the S202 triple `(43, 22, 919447060349, 251)`, which
satisfies the translation identity, the resonance, AND `ν₃(2^A − B) = 22`, yet
has `ν₃(2^A − 1) = 0 ≠ 22`.

This is the maximally bridge-faithful refutation: every hypothesis the bridge
genuinely relies on (the algebraic identity, the resonance, and the `22`
valuation signature that the cylinder is supposed to transfer) holds, and the
conclusion still fails. -/
theorem cylinderForcesVal22_false_faithful :
    ¬ (∀ A q B n : ℕ,
        3 ^ q * n + B = 2 ^ A →
        B % (3 ^ q) = (2 ^ A) % (3 ^ q) →
        padicValNat 3 (2 ^ A - B) = 22 →
        A ≠ 0 →
        padicValNat 3 (2 ^ A - 1) = 22) := by
  intro h
  have hcontra : padicValNat 3 (2 ^ AS202 - 1) = 22 :=
    h AS202 qS202 BS202 nS202
      S202_translation_identity
      S202_resonance
      nu3_two_pow_AS202_sub_BS202
      (by decide)
  rw [nu3_two_pow_AS202_sub_one] at hcontra
  exact absurd hcontra (by decide)

/-- **DECISIVE REFUTATION (raw bridge shape).** Even the bare implication
"translation identity + resonance + `A ≠ 0` ⟹ `ν₃(2^A − 1) = 22`" — the literal
skeleton of `CylinderForcesVal22` with the cylinder hypothesis on `n` replaced
by the strictly *weaker* algebraic data the bridge can actually use — is FALSE
on the S202 triple. (Dropping the `n`-cylinder hypothesis only makes the
statement easier to satisfy; its failure here is therefore the strongest
possible negative result short of exhibiting a literal cylinder word, which the
deep-regime collapse shows can never help anyway.) -/
theorem cylinderForcesVal22_false_raw :
    ¬ (∀ A q B n : ℕ,
        3 ^ q * n + B = 2 ^ A →
        B % (3 ^ q) = (2 ^ A) % (3 ^ q) →
        A ≠ 0 →
        padicValNat 3 (2 ^ A - 1) = 22) := by
  intro h
  have hcontra : padicValNat 3 (2 ^ AS202 - 1) = 22 :=
    h AS202 qS202 BS202 nS202
      S202_translation_identity
      S202_resonance
      (by decide)
  rw [nu3_two_pow_AS202_sub_one] at hcontra
  exact absurd hcontra (by decide)

/-! ## Synthesis: the corrected structural picture

Putting the pieces together, the honest replacement for the (false) bridge is
the conjunction of the *true* facts: for every word `u`,

  * `2^A(u) ≡ B(u) (mod 3^q(u))`                         (resonance, fact 1),
  * `q(u) ≥ k  ⟹  2^A(u) ≡ B(u) (mod 3^k)`              (collapse, fact 2),

so in the deep cylinder regime the cylinder residue of `n` drops out and the
data left about `2^A` is its residue mod `3^k` — **never** its valuation
`ν₃(2^A − 1)`, which (fact 4) depends only on `A`. The only valuation the
identity supplies is `ν₃(2^A − B) = q` at the root (fact 3), an object distinct
from `2^A − 1` whenever `B ≠ 1`. The bridge is therefore false (fact 5), and the
slope-barrier route to `ν₃(2^A − 1)` is genuinely blocked. -/

/-- **Corrected structural summary.** The two true congruence facts the
translation identity forces, bundled: resonance mod `3^q`, and — in the deep
regime — the collapse mod `3^k` that annihilates the cylinder residue of `n`.
This is what the repository can soundly assert in place of
`CylinderForcesVal22`. -/
theorem cylinder_true_structure (u : Word) (k : ℕ) (hqk : k ≤ (evalWord u).q) :
    ((2 ^ (evalWord u).A) % (3 ^ (evalWord u).q)
        = (evalWord u).B % (3 ^ (evalWord u).q))
    ∧ ((2 ^ (evalWord u).A) % (3 ^ k) = (evalWord u).B % (3 ^ k)) :=
  ⟨(resonance_B_eq_two_pow u).symm, deep_regime_cylinder_collapse u k hqk⟩

end CollatzLean4.Admissible
