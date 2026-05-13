/-
S212 — Forward direction of the path-word correspondence.

Given an admissible word `u` ending in a state whose cylinder
representative matches `aS202` at base precision `R`, we *construct*
a weighted path in the inverse cylinder graph from `InvStart m` (the
m-th cylinder of `aS202`) to a goal vertex (the cylinder of `1`),
with total weight equal to `defect (evalWord u)`.

The proof works by structural induction on `u`. The key per-step
lemmas (`step_one_inverse_edge`, `step_zero_inverse_edge`) say that a
single forward branch step in the admissible state machine corresponds
to a single inverse edge of the inverse cylinder graph, with the
correct weight.

Closes S212.1 (forward direction). The reverse direction S212.2
(every inverse-graph path gives an admissible word) is the
remaining conjecture in `PathWordCorrespondence.lean`.
-/

import CollatzLean4.PathWordCorrespondence
import CollatzLean4.CylinderStability

namespace CollatzLean4.Admissible

/-! ### Helpers: `tau` and `InX` depend only on `% 9` -/

/-- `tau (n % 3^k) = tau n` whenever `k ≥ 2`. -/
theorem tau_mod_pow (n k : Nat) (hk : 2 ≤ k) :
    tau (n % 3 ^ k) = tau n := by
  have h9_dvd : (9 : Nat) ∣ 3 ^ k := by
    have h : (3 : Nat) ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk
    rwa [show (3 : Nat) ^ 2 = 9 from by norm_num] at h
  rw [tau_mod, Nat.mod_mod_of_dvd n h9_dvd, ← tau_mod]

/-- `InX (n % 3^k)` follows from `InX n` whenever `k ≥ 2`. -/
theorem InX_mod_pow (n k : Nat) (h : InX n) (hk : 2 ≤ k) :
    InX (n % 3 ^ k) := by
  have h9_dvd : (9 : Nat) ∣ 3 ^ k := by
    have h2 : (3 : Nat) ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk
    rwa [show (3 : Nat) ^ 2 = 9 from by norm_num] at h2
  unfold InX at h ⊢
  rwa [Nat.mod_mod_of_dvd n h9_dvd]

/-! ### Modular arithmetic helper -/

/-- For any `x` and `k`, `(3 · x) mod 3^(k+1) = (3 · (x mod 3^k)) mod 3^(k+1)`.
This expresses that a `Branch.zero` inverse-step preserves the
cylinder representative up to one extra factor of `3`. -/
theorem three_mul_mod_pow_succ (x k : Nat) :
    (3 * x) % 3 ^ (k + 1) = (3 * (x % 3 ^ k)) % 3 ^ (k + 1) := by
  have hk : x = 3 ^ k * (x / 3 ^ k) + x % 3 ^ k := (Nat.div_add_mod x _).symm
  conv_lhs =>
    rw [hk, Nat.mul_add,
        show 3 * (3 ^ k * (x / 3 ^ k)) = 3 ^ (k + 1) * (x / 3 ^ k)
          from by rw [pow_succ]; ring,
        Nat.add_comm]
  rw [Nat.add_mul_mod_self_left]

/-! ### Per-step inverse-edge lemmas -/

/-- After a forward `Branch.one` step from admissible state `s`, the
cylinder pair `(j, (step s 1).n mod 3^(R+j)) → (j, s.n mod 3^(R+j))`
forms a valid inverse-one-edge with weight `τ(s.n)`. -/
theorem step_one_inverse_edge (R : Nat) (s : AdmState) (h : InX s.n)
    (j : Nat) (h_pos : 2 ≤ R + j) :
    InvEdgeOne R
      ⟨j, (step s Branch.one).n % 3 ^ (R + j)⟩
      ⟨j, s.n % 3 ^ (R + j)⟩
      (tau s.n : Int) := by
  refine ⟨rfl, InX_mod_pow s.n (R + j) h h_pos, ?_, ?_⟩
  · -- v.c % M = (2^τ(v'.c) · v'.c) % M
    show ((step s Branch.one).n % 3 ^ (R + j)) % 3 ^ (R + j)
       = (2 ^ tau (s.n % 3 ^ (R + j)) * (s.n % 3 ^ (R + j))) % 3 ^ (R + j)
    rw [Nat.mod_mod, tau_mod_pow s.n (R + j) h_pos]
    show (2 ^ tau s.n * s.n) % 3 ^ (R + j)
       = (2 ^ tau s.n * (s.n % 3 ^ (R + j))) % 3 ^ (R + j)
    exact (Nat.mod_modEq s.n _).symm.mul_left _
  · -- ω = τ(v'.c)
    show (tau s.n : Int) = (tau (s.n % 3 ^ (R + j)) : Int)
    rw [tau_mod_pow s.n (R + j) h_pos]

/-- After a forward `Branch.zero` step from admissible state `s` (with
`GoodState s` for integrality), the cylinder pair
`(j, (step s 0).n mod 3^(R+j)) → (j+1, s.n mod 3^(R+j+1))` forms a
valid inverse-zero-edge with weight `τ(s.n) − 2`. -/
theorem step_zero_inverse_edge (R : Nat) (s : AdmState)
    (h : InX s.n) (j : Nat) (h_pos : 2 ≤ R + j) :
    InvEdgeZero R
      ⟨j, (step s Branch.zero).n % 3 ^ (R + j)⟩
      ⟨j + 1, s.n % 3 ^ (R + j + 1)⟩
      ((tau s.n : Int) - 2) := by
  refine ⟨rfl, InX_mod_pow s.n (R + j + 1) h (by omega), ?_, ?_⟩
  · -- (3 * v.c + 1) % 3^(R+j+1) = (2^τ(v'.c) · v'.c) % 3^(R+j+1)
    -- v.c = (step s Branch.zero).n % 3^(R+j)
    -- (step s Branch.zero).n = (2^τ(s.n) · s.n − 1) / 3
    -- Integrality: 3 ∣ 2^τ(s.n) · s.n − 1 ⇒ 3 · (step s 0).n + 1 = 2^τ(s.n) · s.n
    have h_int : 3 ∣ (2 ^ tau s.n * s.n - 1) := psiZero_integrality h
    have h_pos_mul : 1 ≤ 2 ^ tau s.n * s.n := by
      have hmod := psiZero_mul_mod h; omega
    have h_step : (step s Branch.zero).n = (2 ^ tau s.n * s.n - 1) / 3 := rfl
    have h_three : 3 * (step s Branch.zero).n + 1 = 2 ^ tau s.n * s.n := by
      rw [h_step]
      obtain ⟨k, hk⟩ := h_int
      omega
    show (3 * ((step s Branch.zero).n % 3 ^ (R + j)) + 1) % 3 ^ (R + j + 1)
       = (2 ^ tau (s.n % 3 ^ (R + j + 1)) * (s.n % 3 ^ (R + j + 1)))
           % 3 ^ (R + j + 1)
    rw [tau_mod_pow s.n (R + j + 1) (by omega)]
    -- LHS rewrite: 3 * (x % 3^(R+j)) % 3^(R+j+1) = (3*x) % 3^(R+j+1)
    -- So adding +1: (3 * (x % 3^(R+j)) + 1) % 3^(R+j+1) = (3*x + 1) % 3^(R+j+1)
    have h_mod : (3 * ((step s Branch.zero).n % 3 ^ (R + j)) + 1) % 3 ^ (R + j + 1)
               = (3 * (step s Branch.zero).n + 1) % 3 ^ (R + j + 1) := by
      conv_rhs => rw [Nat.add_mod, three_mul_mod_pow_succ, ← Nat.add_mod]
    rw [h_mod, h_three]
    -- Now goal: (2^τ · s.n) % 3^(R+j+1) = (2^τ · (s.n % 3^(R+j+1))) % 3^(R+j+1)
    exact (Nat.mod_modEq s.n _).symm.mul_left _
  · -- ω = τ(v'.c) − 2
    show (tau s.n : Int) - 2
       = (tau (s.n % 3 ^ (R + j + 1)) : Int) - 2
    rw [tau_mod_pow s.n (R + j + 1) (by omega)]

/-! ### Path append lemma -/

/-- Extend a weighted path by appending an edge at the end. The new
intermediate vertex list is the original list concatenated with `[t']`
(the new target). -/
theorem WPath_append_edge {V : Type} (edge : V → V → Int → Prop)
    {s t t' : V} {w ω : Int} {vs : List V}
    (h_path : WPath edge s t w vs) (h_edge : edge t t' ω) :
    WPath edge s t' (w + ω) (vs ++ [t']) := by
  induction vs generalizing s w with
  | nil =>
      simp only [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      show WPath edge s t' (0 + ω) [t']
      refine ⟨ω, 0, h_edge, ⟨rfl, rfl⟩, by ring⟩
  | cons v vs ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_e, h_rest, rfl⟩ := h_path
      show WPath edge s t' (ω₁ + ω₂ + ω) ((v :: vs) ++ [t'])
      rw [List.cons_append]
      refine ⟨ω₁, ω₂ + ω, h_e, ih h_rest, by ring⟩

/-! ### S212 forward direction — general form -/

/-- **S212 forward (general form)**: every admissible word `u`, run
from any state `s` with `Inv s`, traces a weighted path in the
inverse cylinder graph from `(0, (runWord u s).n mod 3^R)` to
`(numZeros u, s.n mod 3^(R + numZeros u))` of total weight equal to
`defect (runWord u s) − defect s`.

Proof by structural induction on `u`, using `step_one_inverse_edge` /
`step_zero_inverse_edge` to extend the path by one inverse edge at
each step. -/
theorem S212_forward_general (R : Nat) (h_R : 2 ≤ R)
    (u : Word) (s : AdmState) (h_inv : Inv s) :
    ∃ vs : List InvVertex,
      WPath (InvEdge R)
        ⟨0, (runWord u s).n % 3 ^ R⟩
        ⟨Word.numZeros u, s.n % 3 ^ (R + Word.numZeros u)⟩
        (defect (runWord u s) - defect s) vs ∧
      (∀ v ∈ vs, v.c < 3 ^ (R + v.j)) := by
  induction u generalizing s with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · refine ⟨rfl, ?_⟩
        show defect s - defect s = 0
        ring
      · intro v hv; exact absurd hv List.not_mem_nil
  | cons b u' ih =>
      have h_inv' : Inv (step s b) := step_inv h_inv b
      obtain ⟨vs', h_path', h_can'⟩ := ih (step s b) h_inv'
      cases b with
      | one =>
          have h_edge : InvEdge R
              ⟨Word.numZeros u', (step s Branch.one).n % 3 ^ (R + Word.numZeros u')⟩
              ⟨Word.numZeros u', s.n % 3 ^ (R + Word.numZeros u')⟩
              (tau s.n : Int) :=
            Or.inl (step_one_inverse_edge R s h_inv.2 (Word.numZeros u') (by omega))
          have h_append := WPath_append_edge (InvEdge R) h_path' h_edge
          refine ⟨vs' ++ [⟨Word.numZeros u', s.n % 3 ^ (R + Word.numZeros u')⟩],
                  ?_, ?_⟩
          · show WPath (InvEdge R)
                ⟨0, (runWord u' (step s Branch.one)).n % 3 ^ R⟩
                ⟨Word.numZeros (Branch.one :: u'),
                 s.n % 3 ^ (R + Word.numZeros (Branch.one :: u'))⟩
                (defect (runWord u' (step s Branch.one)) - defect s) _
            simp only [Word.numZeros_cons_one]
            have h_w : defect (runWord u' (step s Branch.one)) - defect s
                     = defect (runWord u' (step s Branch.one))
                       - defect (step s Branch.one) + (tau s.n : Int) := by
              rw [defect_step_one]; ring
            rw [h_w]
            exact h_append
          · intro v hv
            rcases List.mem_append.mp hv with h_in_vs' | h_in_last
            · exact h_can' v h_in_vs'
            · rcases List.mem_singleton.mp h_in_last with rfl
              exact Nat.mod_lt _ (by positivity)
      | zero =>
          have h_edge : InvEdge R
              ⟨Word.numZeros u', (step s Branch.zero).n % 3 ^ (R + Word.numZeros u')⟩
              ⟨Word.numZeros u' + 1, s.n % 3 ^ (R + Word.numZeros u' + 1)⟩
              ((tau s.n : Int) - 2) :=
            Or.inr (step_zero_inverse_edge R s h_inv.2 (Word.numZeros u') (by omega))
          have h_append := WPath_append_edge (InvEdge R) h_path' h_edge
          refine ⟨vs' ++ [⟨Word.numZeros u' + 1,
                            s.n % 3 ^ (R + Word.numZeros u' + 1)⟩],
                  ?_, ?_⟩
          · show WPath (InvEdge R)
                ⟨0, (runWord u' (step s Branch.zero)).n % 3 ^ R⟩
                ⟨Word.numZeros (Branch.zero :: u'),
                 s.n % 3 ^ (R + Word.numZeros (Branch.zero :: u'))⟩
                (defect (runWord u' (step s Branch.zero)) - defect s) _
            simp only [Word.numZeros_cons_zero]
            have h_w : defect (runWord u' (step s Branch.zero)) - defect s
                     = defect (runWord u' (step s Branch.zero))
                       - defect (step s Branch.zero) + ((tau s.n : Int) - 2) := by
              rw [defect_step_zero]; ring
            rw [h_w]
            exact h_append
          · intro v hv
            rcases List.mem_append.mp hv with h_in_vs' | h_in_last
            · exact h_can' v h_in_vs'
            · rcases List.mem_singleton.mp h_in_last with rfl
              exact Nat.mod_lt _ (by positivity)

/-! ### Specialization: forward direction at `s = initState` -/

/-- **S212.1**: the forward half of the path-word correspondence at the
m-th S202 cylinder. Every admissible word `u` landing in the m-th
cylinder (i.e., `n(u) ≡ aS202 (mod 3^(22m+2))`) traces a weighted
path from `InvStart m` to a goal vertex of weight `defect (evalWord u)`.

Closes S212.1. -/
theorem S212_forward (m : Nat)
    (u : Word) (h_cyl : (evalWord u).n % (3 ^ (22 * m + 2))
                         = aS202 % (3 ^ (22 * m + 2))) :
    ∃ (vs : List InvVertex) (goal : InvVertex),
      InvVertex.IsGoal goal (22 * m + 2) ∧
      goal.j = Word.numZeros u ∧
      (∀ v ∈ vs, v.c < 3 ^ (22 * m + 2 + v.j)) ∧
      WPath (InvEdge (22 * m + 2)) (InvStart m) goal
            (defect (evalWord u)) vs := by
  obtain ⟨vs, h_path, h_can⟩ :=
    S212_forward_general (22 * m + 2) (by omega) u initState init_inv
  refine ⟨vs, ⟨Word.numZeros u,
              initState.n % 3 ^ (22 * m + 2 + Word.numZeros u)⟩,
          ?_, rfl, h_can, ?_⟩
  · -- Goal condition: the end vertex's cylinder representative ≡ 1.
    unfold InvVertex.IsGoal
    show ((1 : Nat) % 3 ^ (22 * m + 2 + Word.numZeros u))
            % 3 ^ (22 * m + 2 + Word.numZeros u)
       = 1 % 3 ^ (22 * m + 2 + Word.numZeros u)
    exact Nat.mod_mod _ _
  · -- Translate the general theorem's start vertex (using `initState`)
    -- to the form `InvStart m`. `initState.n = 1`, and `aS202 ≡ n(u) (mod 3^R)`.
    show WPath (InvEdge (22 * m + 2)) (InvStart m) _ _ _
    have h_start_eq :
        (InvStart m : InvVertex)
          = ⟨0, (runWord u initState).n % 3 ^ (22 * m + 2)⟩ := by
      show (⟨0, aS202 % 3 ^ (22 * m + 2)⟩ : InvVertex)
         = ⟨0, (evalWord u).n % 3 ^ (22 * m + 2)⟩
      rw [h_cyl]
    have h_defect : defect (evalWord u)
                  = defect (runWord u initState) - defect initState := by
      show defect (runWord u initState) = _
      have : defect initState = 0 := by simp [defect, initState]
      omega
    rw [h_start_eq, h_defect]
    exact h_path

/-! ### Updated barrier chain — S212.1 no longer hypothetical

With `S212_forward` now closed, the original `barrier_chain` (which
took `S212_path_word_correspondence` as a hypothesis) can be replaced
by a version that only requires the remaining open conjecture S216
(closure-to-barrier). -/

/-- **Barrier chain (with S212.1 proven)**: assuming the S216
closure-to-barrier conjecture, every `LiftedCertificate` produces a
formal lower bound `T ≤ D(u)` on the defect of every admissible word
`u` landing in the m-th S202 cylinder. -/
theorem barrier_chain_with_forward
    (m Q T : Nat)
    (h_S216 : S216_closure_to_barrier_conjecture m Q T)
    (cert : LiftedCertificate m Q T)
    (u : Word)
    (h_cyl : (evalWord u).n % (3 ^ (22 * m + 2))
              = aS202 % (3 ^ (22 * m + 2))) :
    (T : Int) ≤ defect (evalWord u) := by
  obtain ⟨vs, goal, h_g, _h_j_eq, _h_can, h_path⟩ := S212_forward m u h_cyl
  exact h_S216 cert vs goal _ h_g h_path

end CollatzLean4.Admissible
