/-
Admissible and free translation sets B_adm, B_free, R_adm, R_free,
and the equivalence between word-coverage and translation-coverage.
-/

import CollatzLean4.AdmissibleBasic

namespace CollatzLean4.Admissible

def B_adm (A q B : Nat) : Prop :=
  ∃ w : Word,
    (evalWord w).A = A ∧ (evalWord w).q = q ∧ (evalWord w).B = B

def P_adm (A q : Nat) : Prop := ∃ B, B_adm A q B

def R_adm (A q B : Nat) : Prop :=
  B_adm A q B ∧ B % (3 ^ q) = (2 ^ A) % (3 ^ q)

/-- Free B's, built from strictly-decreasing exponent lists  c_m < A.  -/
def B_of_cs : List Nat → Nat
  | []        => 0
  | c :: cs   => 2 ^ c + 3 * B_of_cs cs

def StrictDecBelow (A : Nat) (cs : List Nat) : Prop :=
  (∀ c ∈ cs, c < A) ∧ cs.Pairwise (· > ·)

def B_free (A q B : Nat) : Prop :=
  ∃ cs : List Nat,
    cs.length = q ∧ StrictDecBelow A cs ∧ B_of_cs cs = B

def R_free (A q B : Nat) : Prop :=
  B_free A q B ∧ B % (3 ^ q) = (2 ^ A) % (3 ^ q)

def InImageTheta (n : Nat) : Prop := ∃ w : Word, (evalWord w).n = n

/-- S191-E: equivalence between word-coverage and translation-coverage.
    Forward: pack the (A, q, B) read off `evalWord w` and use the translation
    identity. Backward: from the abstract triple, recover the word via
    `B_adm`, then use the identity to cancel `3^q` and recover `n`. -/
theorem coverage_translation_equiv :
    (∀ n : Nat, InX n → InImageTheta n)
    ↔
    (∀ n : Nat, InX n →
      ∃ A q B : Nat, B_adm A q B ∧ 3 ^ q * n + B = 2 ^ A) := by
  constructor
  · intro h n hn
    obtain ⟨w, hw⟩ := h n hn
    refine ⟨(evalWord w).A, (evalWord w).q, (evalWord w).B,
            ⟨w, rfl, rfl, rfl⟩, ?_⟩
    have := evalWord_translation_identity w
    unfold GoodState at this
    rw [hw] at this
    exact this
  · intro h n hn
    obtain ⟨A, q, B, ⟨w, hwA, hwq, hwB⟩, heq⟩ := h n hn
    refine ⟨w, ?_⟩
    have hgood := evalWord_translation_identity w
    unfold GoodState at hgood
    rw [hwA, hwq, hwB] at hgood
    have hpos : 0 < 3 ^ q := by positivity
    have hmul : 3 ^ q * (evalWord w).n = 3 ^ q * n := by omega
    exact Nat.eq_of_mul_eq_mul_left hpos hmul

/-! ### S192-A: automatic resonance

Every admissible triple is resonant: `B ≡ 2^A (mod 3^q)`. Immediate from
the translation identity `3^q · n + B = 2^A` — the resonance condition is
not an extra constraint on `B_adm` but a free corollary. -/

theorem B_adm_resonance {A q B : Nat} (h : B_adm A q B) :
    B % (3 ^ q) = (2 ^ A) % (3 ^ q) := by
  obtain ⟨w, hA, hq, hB⟩ := h
  have hres := evalWord_resonance_mod w
  rw [hA, hq, hB] at hres
  exact hres

/-- `R_adm` is just `B_adm` — the resonance is automatic. -/
theorem R_adm_iff_B_adm (A q B : Nat) : R_adm A q B ↔ B_adm A q B :=
  ⟨And.left, fun h => ⟨h, B_adm_resonance h⟩⟩

/-! ### S192–S195 (forward): `B_adm → B_free`

Every B reachable by an admissible word has the form
`Σ_{i=1}^{q} 3^{i-1} · 2^{c_i}` for strictly-decreasing exponents
`A > c_1 > c_2 > … > c_q ≥ 0`. The list `cs` is built incrementally:
each `one` step shifts every existing exponent by `τ`; each `zero` step
shifts and appends a fresh `0`.

The reverse direction (`B_free → B_adm`) does NOT hold in general: a
combinatorial list `cs` need not arise from any actual run, because the
`τ`-pattern along the path is constrained by the dynamics. -/

lemma B_of_cs_map_add (cs : List Nat) (t : Nat) :
    B_of_cs (cs.map (· + t)) = 2 ^ t * B_of_cs cs := by
  induction cs with
  | nil => simp [B_of_cs]
  | cons c cs ih =>
    rw [List.map_cons, B_of_cs, B_of_cs, ih, pow_add]
    ring

lemma B_of_cs_append_zero (cs : List Nat) :
    B_of_cs (cs ++ [0]) = B_of_cs cs + 3 ^ cs.length := by
  induction cs with
  | nil => simp [B_of_cs]
  | cons c cs ih =>
    rw [List.cons_append, B_of_cs, B_of_cs, ih, List.length_cons, pow_succ]
    ring

/-- `τ ≥ 1` on `X`: the smallest value is `1` (for `n % 9 ∈ {2, 8}`). -/
lemma tau_pos {n : Nat} (h : InX n) : 1 ≤ tau n := by
  have htau : tau n = tau (n % 9) := by unfold tau; rw [Nat.mod_mod]
  unfold InX at h
  rcases h with h | h | h | h | h | h <;>
    (rw [htau, h]; unfold tau; decide)

private lemma pairwise_gt_map_add {cs : List Nat} {t : Nat}
    (h : cs.Pairwise (· > ·)) :
    (cs.map (· + t)).Pairwise (· > ·) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.pairwise_cons] at h
    simp only [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih h.2⟩
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have := h.1 x' hx'
    omega

private lemma sdb_map_add {A t : Nat} {cs : List Nat}
    (h : StrictDecBelow A cs) :
    StrictDecBelow (A + t) (cs.map (· + t)) := by
  refine ⟨?_, pairwise_gt_map_add h.2⟩
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  have := h.1 c' hc'
  omega

private lemma sdb_append_zero_shift {A t : Nat} {cs : List Nat}
    (h : StrictDecBelow A cs) (ht : 1 ≤ t) :
    StrictDecBelow (A + t) ((cs.map (· + t)) ++ [0]) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      have := h.1 c' hc'
      omega
    · rw [List.mem_singleton] at hc
      omega
  · rw [List.pairwise_append]
    refine ⟨pairwise_gt_map_add h.2, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_map] at ha
    obtain ⟨a', _, rfl⟩ := ha
    rw [List.mem_singleton] at hb
    omega

/-- Generalized form: from any `Inv`-respecting starting state already
represented by a strict-dec list `cs`, every continuation is too. -/
lemma runWord_to_free (w : Word) :
    ∀ (s : AdmState), Inv s →
    ∀ (cs : List Nat), cs.length = s.q → StrictDecBelow s.A cs →
    B_of_cs cs = s.B →
    ∃ cs' : List Nat,
        cs'.length = (runWord w s).q ∧
        StrictDecBelow (runWord w s).A cs' ∧
        B_of_cs cs' = (runWord w s).B := by
  induction w with
  | nil =>
    intros s _ cs hlen hsdb hB
    exact ⟨cs, hlen, hsdb, hB⟩
  | cons b bs ih =>
    intros s hs cs hlen hsdb hB
    cases b with
    | one =>
      refine ih (step s Branch.one) (step_inv hs Branch.one)
             (cs.map (· + tau s.n)) ?_ ?_ ?_
      · simp [step, hlen]
      · have hA : (step s Branch.one).A = s.A + tau s.n := rfl
        rw [hA]; exact sdb_map_add hsdb
      · show B_of_cs (cs.map (· + tau s.n)) = (step s Branch.one).B
        rw [B_of_cs_map_add, hB]; rfl
    | zero =>
      refine ih (step s Branch.zero) (step_inv hs Branch.zero)
             ((cs.map (· + tau s.n)) ++ [0]) ?_ ?_ ?_
      · simp [step, hlen]
      · have hA : (step s Branch.zero).A = s.A + tau s.n := rfl
        rw [hA]; exact sdb_append_zero_shift hsdb (tau_pos hs.2)
      · show B_of_cs ((cs.map (· + tau s.n)) ++ [0]) = (step s Branch.zero).B
        rw [B_of_cs_append_zero, List.length_map, B_of_cs_map_add, hB, hlen]
        rfl

/-- S192–S195 (forward): every admissible triple admits a free-list
representation. -/
theorem B_adm_imp_B_free {A q B : Nat} (h : B_adm A q B) : B_free A q B := by
  obtain ⟨w, hA, hq, hB⟩ := h
  have hsdb : StrictDecBelow initState.A ([] : List Nat) := by
    refine ⟨?_, List.Pairwise.nil⟩
    intro c hc
    simp at hc
  obtain ⟨cs, hclen, hcsdb, hcB⟩ :=
    runWord_to_free w initState init_inv [] rfl hsdb rfl
  refine ⟨cs, ?_, ?_, ?_⟩
  · rw [hclen]; exact hq
  · rw [← hA]; exact hcsdb
  · rw [hcB]; exact hB

end CollatzLean4.Admissible
