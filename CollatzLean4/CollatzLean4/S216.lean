/-
S216 — Closure-to-barrier with Bellman-Ford optimistic closure.

The Python engine's old "naïve" cut (`d < T`) is INCORRECT for a
formal barrier when the inverse graph has negative edges: a path can
exceed cost `T` temporarily and descend below later via negative
zero-edges (τ−2 = −1 when α ∈ {2, 8}).

The correct closure rule is **optimistic**: a state-cost pair `(v, d)`
is *relevant* iff `d − (Q − j(v)) < T`, where `Q − j(v)` is the
maximum descent still available (number of inverse-zero-edges left,
each contributing at most `−1`).

This module:

  * Defines `credit`, `relevant`, and the `S216Cert` structure.
  * Proves `tau_ge_one`, `InvEdge_weight_lower_bound`, and the key
    `suffix_weight_bound`: any sub-path from `v` has weight
    `≥ −(Q − v.j)`.
  * States `closure_to_barrier`: from an S216 certificate plus a
    path of weight `< T` to a goal, derive `False`.

`closure_to_barrier` is the BF correctness induction. The lower
bound `suffix_weight_bound` makes every prefix automatically
relevant (lemma S216.2 in the paper). The induction propagates
`dist ≤ prefix_cost`, ending with `dist(goal) < T`, contradicting
the goal-cond of the certificate.
-/

import CollatzLean4.S212Forward
import CollatzLean4.OverCover

namespace CollatzLean4.Admissible

/-! ### Modular inverse of `2` modulo `3^k`

`invMod2 M := (M+1)/2`. For `M = 3^k` with `k ≥ 1`, this satisfies
`2 · invMod2 M ≡ 1 (mod M)` since `M` is odd. -/

/-- `2 · invMod2 (3^k) ≡ 1 (mod 3^k)` for `k ≥ 1`. -/
theorem invMod2_three_pow_spec (k : Nat) (hk : 1 ≤ k) :
    (2 * invMod2 (3 ^ k)) % (3 ^ k) = 1 := by
  unfold invMod2
  have h_odd : Odd (3 ^ k) := Odd.pow (by decide : Odd 3)
  obtain ⟨m, hm⟩ := h_odd
  have h_div : (3 ^ k + 1) / 2 = m + 1 := by omega
  rw [h_div]
  have h_mul : 2 * (m + 1) = 3 ^ k + 1 := by omega
  rw [h_mul]
  have h_lt : 1 < 3 ^ k := by
    have h : (3 : Nat) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk
    have h31 : (3 : Nat) ^ 1 = 3 := by ring
    omega
  -- (3^k + 1) % 3^k = (1 + 3^k) % 3^k = 1 % 3^k = 1
  rw [show 3 ^ k + 1 = 1 + 3 ^ k from by ring, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h_lt

/-- Powers of the modular inverse: `2^τ · (invMod2 (3^k))^τ ≡ 1 (mod 3^k)`. -/
theorem two_pow_mul_invMod2Pow_three_pow (k τ : Nat) (hk : 1 ≤ k) :
    (2 ^ τ * (invMod2 (3 ^ k)) ^ τ) % (3 ^ k) = 1 % (3 ^ k) := by
  have h_base : (2 * invMod2 (3 ^ k)) % (3 ^ k) = 1 % (3 ^ k) := by
    rw [invMod2_three_pow_spec k hk]
    have h_lt : 1 < 3 ^ k := by
      have h : (3 : Nat) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk
      have h31 : (3 : Nat) ^ 1 = 3 := by ring
      omega
    rw [Nat.mod_eq_of_lt h_lt]
  -- Lift the base ModEq through `pow`.
  have hME : (2 * invMod2 (3 ^ k)) ≡ 1 [MOD 3 ^ k] := h_base
  have hME_pow : (2 * invMod2 (3 ^ k)) ^ τ ≡ 1 ^ τ [MOD 3 ^ k] := hME.pow τ
  rw [one_pow] at hME_pow
  have h_eq : (2 * invMod2 (3 ^ k)) ^ τ = 2 ^ τ * (invMod2 (3 ^ k)) ^ τ := by
    rw [mul_pow]
  rw [← h_eq]
  exact hME_pow

/-! ### outgoingEdges soundness: every produced edge is a valid InvEdge

The certificate engine enumerates edges via `outgoingEdges R Q v`. To
lift a JSON certificate to a Lean `S216Cert` we need: every produced
edge satisfies `InvEdge R v v' ω`.

The proof unfolds `filterMap` and verifies the four conditions of
`InvEdgeOne` (resp. `InvEdgeZero`) for the canonical target
`y = (invMod2 M)^τ · v.c mod M` (resp. `... · (3·v.c+1) mod M'`). The
key modular fact `2^τ · y ≡ v.c (mod M)` follows from
`two_pow_mul_invMod2Pow_three_pow`. -/

/-- Helper: if `y ≡ α (mod 9)` and `α ∈ [1, 2, 4, 5, 7, 8]`, then `InX y`. -/
private theorem InX_of_mod_alpha (y α : Nat)
    (hα : α ∈ [(1 : Nat), 2, 4, 5, 7, 8])
    (hy : y % 9 = α) : InX y := by
  unfold InX
  rw [hy]
  fin_cases hα <;> tauto

/-- Helper: `tau y = tau α` when `y % 9 = α`. -/
private theorem tau_eq_of_mod (y α : Nat) (hy : y % 9 = α) : tau y = tau α := by
  rw [tau_mod, hy]

/-- One-edge soundness for a specific α. -/
private theorem oneEdge_inv_alpha (R : Nat) (v : InvVertex) (α : Nat)
    (hα : α ∈ [(1 : Nat), 2, 4, 5, 7, 8])
    (hR : 1 ≤ R + v.j)
    (hy_alpha :
      (invMod2Pow (tau α) (3 ^ (R + v.j)) * v.c % (3 ^ (R + v.j))) % 9 = α) :
    let M := 3 ^ (R + v.j)
    let y := invMod2Pow (tau α) M * v.c % M
    InvEdgeOne R v ⟨v.j, y⟩ ((tau α : Int)) := by
  simp only
  set M := 3 ^ (R + v.j) with hM
  set y := invMod2Pow (tau α) M * v.c % M with hy
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact InX_of_mod_alpha y α hα hy_alpha
  · -- v.c % M = (2^τ · y) % M
    have h_tau_y : tau y = tau α := tau_eq_of_mod y α hy_alpha
    show v.c % M = (2 ^ tau y * y) % M
    rw [h_tau_y]
    -- ModEq chain: y ≡ invMod2 M ^ τ * v.c (mod M)
    have hy_me : y ≡ invMod2 M ^ tau α * v.c [MOD M] := by
      show y % M = (invMod2 M ^ tau α * v.c) % M
      rw [hy]
      unfold invMod2Pow
      rw [Nat.mod_mod]
      rw [Nat.mul_mod (invMod2 M ^ tau α % M), Nat.mod_mod,
          ← Nat.mul_mod]
    have h_inv : 2 ^ tau α * invMod2 M ^ tau α ≡ 1 [MOD M] := by
      show (2 ^ tau α * invMod2 M ^ tau α) % M = 1 % M
      exact two_pow_mul_invMod2Pow_three_pow _ _ hR
    have h_final : 2 ^ tau α * y ≡ v.c [MOD M] := by
      calc 2 ^ tau α * y
          ≡ 2 ^ tau α * (invMod2 M ^ tau α * v.c) [MOD M] := hy_me.mul_left _
        _ = (2 ^ tau α * invMod2 M ^ tau α) * v.c := by ring
        _ ≡ 1 * v.c [MOD M] := h_inv.mul_right v.c
        _ = v.c := by ring
    exact h_final.symm
  · -- ω = τ(y) = τ(α)
    show (tau α : Int) = (tau y : Int)
    rw [tau_eq_of_mod y α hy_alpha]

/-- Zero-edge soundness for a specific α. -/
private theorem zeroEdge_inv_alpha (R : Nat) (v : InvVertex) (α : Nat)
    (hα : α ∈ [(1 : Nat), 2, 4, 5, 7, 8])
    (hy_alpha :
      (invMod2Pow (tau α) (3 ^ (R + v.j + 1)) * (3 * v.c + 1)
        % (3 ^ (R + v.j + 1))) % 9 = α) :
    let M' := 3 ^ (R + v.j + 1)
    let y := invMod2Pow (tau α) M' * (3 * v.c + 1) % M'
    InvEdgeZero R v ⟨v.j + 1, y⟩ ((tau α : Int) - 2) := by
  simp only
  set M' := 3 ^ (R + v.j + 1) with hM'
  set y := invMod2Pow (tau α) M' * (3 * v.c + 1) % M' with hy
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact InX_of_mod_alpha y α hα hy_alpha
  · -- (3 · v.c + 1) % M' = (2^τ · y) % M'
    have h_tau_y : tau y = tau α := tau_eq_of_mod y α hy_alpha
    show (3 * v.c + 1) % M' = (2 ^ tau y * y) % M'
    rw [h_tau_y]
    have hR' : 1 ≤ R + v.j + 1 := by omega
    have hy_me : y ≡ invMod2 M' ^ tau α * (3 * v.c + 1) [MOD M'] := by
      show y % M' = (invMod2 M' ^ tau α * (3 * v.c + 1)) % M'
      rw [hy]
      unfold invMod2Pow
      rw [Nat.mod_mod]
      rw [Nat.mul_mod (invMod2 M' ^ tau α % M'), Nat.mod_mod,
          ← Nat.mul_mod]
    have h_inv : 2 ^ tau α * invMod2 M' ^ tau α ≡ 1 [MOD M'] := by
      show (2 ^ tau α * invMod2 M' ^ tau α) % M' = 1 % M'
      exact two_pow_mul_invMod2Pow_three_pow _ _ hR'
    have h_final : 2 ^ tau α * y ≡ (3 * v.c + 1) [MOD M'] := by
      calc 2 ^ tau α * y
          ≡ 2 ^ tau α * (invMod2 M' ^ tau α * (3 * v.c + 1)) [MOD M'] :=
            hy_me.mul_left _
        _ = (2 ^ tau α * invMod2 M' ^ tau α) * (3 * v.c + 1) := by ring
        _ ≡ 1 * (3 * v.c + 1) [MOD M'] := h_inv.mul_right _
        _ = 3 * v.c + 1 := by ring
    exact h_final.symm
  · show (tau α : Int) - 2 = (tau y : Int) - 2
    rw [tau_eq_of_mod y α hy_alpha]

/-- **`outgoingEdges` soundness**: every produced edge satisfies
`InvEdge R v · ·`. This is the bridge from the certificate engine's
explicit enumeration to the abstract edge relation used in WPath. -/
theorem outgoingEdges_sound
    (R Q : Nat) (v : InvVertex) (hR : 1 ≤ R + v.j) :
    ∀ e ∈ outgoingEdges R Q v, InvEdge R v e.1 e.2 := by
  intro e he
  unfold outgoingEdges at he
  simp only [List.mem_append] at he
  rcases he with h_one | h_zero
  · -- one-edge case: e from oneEdges
    refine Or.inl ?_
    simp only [List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false] at h_one
    obtain ⟨α, hα, h_some⟩ := h_one
    -- Determine α's membership concretely
    have hα_list : α ∈ [(1 : Nat), 2, 4, 5, 7, 8] := by
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    -- The conditional inside filterMap
    by_cases hcond :
        (invMod2Pow (tau α) (3 ^ (R + v.j)) * v.c % (3 ^ (R + v.j))) % 9 = α
    · rw [if_pos hcond] at h_some
      simp only [Option.some.injEq] at h_some
      rw [← h_some]
      exact oneEdge_inv_alpha R v α hα_list hR hcond
    · rw [if_neg hcond] at h_some
      contradiction
  · -- zero-edge case: e from zeroEdges (only if v.j < Q)
    refine Or.inr ?_
    by_cases hQ : v.j < Q
    · rw [if_pos hQ] at h_zero
      simp only [List.mem_filterMap, List.mem_cons, List.not_mem_nil,
                 or_false] at h_zero
      obtain ⟨α, hα, h_some⟩ := h_zero
      have hα_list : α ∈ [(1 : Nat), 2, 4, 5, 7, 8] := by
        rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      by_cases hcond :
          (invMod2Pow (tau α) (3 ^ (R + v.j + 1)) * (3 * v.c + 1)
            % (3 ^ (R + v.j + 1))) % 9 = α
      · rw [if_pos hcond] at h_some
        simp only [Option.some.injEq] at h_some
        rw [← h_some]
        exact zeroEdge_inv_alpha R v α hα_list hcond
      · rw [if_neg hcond] at h_some
        contradiction
    · rw [if_neg hQ] at h_zero
      exact absurd h_zero (List.not_mem_nil)

/-! ### outgoingEdges completeness for canonical vertices

Every canonical InvEdge from a canonical source corresponds to an
entry in `outgoingEdges R Q v`. Combined with soundness, this gives
a bidirectional characterization that bridges Prop-level closures to
Bool-decidable enumeration. -/

/-- Helper: list membership for the admissible alphabet from InX. -/
private theorem InX_to_list (n : Nat) (h : InX n) :
    n % 9 ∈ [(1 : Nat), 2, 4, 5, 7, 8] := by
  unfold InX at h
  rcases h with h | h | h | h | h | h <;> rw [h] <;> simp

/-- Completeness for one-edges with canonical target. -/
theorem outgoingEdges_complete_one
    (R Q : Nat) (v v' : InvVertex) (ω : Int)
    (hv'_can : v'.c < 3 ^ (R + v.j))
    (hR : 1 ≤ R + v.j)
    (h : InvEdgeOne R v v' ω) :
    (v', ω) ∈ outgoingEdges R Q v := by
  obtain ⟨h_j, h_X, h_cong, h_ω⟩ := h
  set α := v'.c % 9 with hα_def
  set M := 3 ^ (R + v.j) with hM_def
  -- α is in the admissible alphabet list
  have hα_list : α ∈ [(1 : Nat), 2, 4, 5, 7, 8] := InX_to_list v'.c h_X
  -- tau v'.c = tau α
  have h_tau_eq : tau v'.c = tau α := by rw [hα_def, ← tau_mod]
  -- The canonical y for this α equals v'.c
  have hy : invMod2Pow (tau α) M * v.c % M = v'.c := by
    rw [← h_tau_eq]
    have h_inv : 2 ^ tau v'.c * invMod2 M ^ tau v'.c ≡ 1 [MOD M] := by
      show (2 ^ tau v'.c * invMod2 M ^ tau v'.c) % M = 1 % M
      exact two_pow_mul_invMod2Pow_three_pow _ _ hR
    -- From v.c ≡ 2^τ · v'.c (mod M), derive invMod2^τ · v.c ≡ v'.c (mod M).
    have h_cong' : v.c ≡ 2 ^ tau v'.c * v'.c [MOD M] := h_cong
    have h_main : invMod2Pow (tau v'.c) M * v.c ≡ v'.c [MOD M] := by
      unfold invMod2Pow
      have step1 : invMod2 M ^ tau v'.c % M * v.c ≡ invMod2 M ^ tau v'.c * v.c [MOD M] := by
        show (invMod2 M ^ tau v'.c % M * v.c) % M = (invMod2 M ^ tau v'.c * v.c) % M
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      calc invMod2 M ^ tau v'.c % M * v.c
          ≡ invMod2 M ^ tau v'.c * v.c [MOD M] := step1
        _ ≡ invMod2 M ^ tau v'.c * (2 ^ tau v'.c * v'.c) [MOD M] := h_cong'.mul_left _
        _ = (2 ^ tau v'.c * invMod2 M ^ tau v'.c) * v'.c := by ring
        _ ≡ 1 * v'.c [MOD M] := h_inv.mul_right _
        _ = v'.c := by ring
    -- Conclude (invMod2Pow τ M * v.c) % M = v'.c using v'.c < M.
    have h_mod : (invMod2Pow (tau v'.c) M * v.c) % M = v'.c % M := h_main
    rw [Nat.mod_eq_of_lt hv'_can] at h_mod
    exact h_mod
  -- The filter condition y % 9 = α
  have hy_alpha : (invMod2Pow (tau α) M * v.c % M) % 9 = α := by
    rw [hy, ← hα_def]
  -- Now show (v', ω) is in oneEdges (the first part of outgoingEdges)
  unfold outgoingEdges
  rw [List.mem_append]
  refine Or.inl ?_
  simp only [List.mem_filterMap]
  refine ⟨α, ?_, ?_⟩
  · -- α ∈ [1, 2, 4, 5, 7, 8]
    simpa using hα_list
  · -- The filterMap produces (⟨v.j, v'.c⟩, τ) = (v', ω)
    show (let τ := tau α; let y := invMod2Pow τ M * v.c % M;
          if y % 9 = α then some (⟨v.j, y⟩, (τ : Int)) else none) = some (v', ω)
    simp only [hy_alpha, if_pos]
    rw [hy]
    -- (⟨v.j, v'.c⟩, tau α) = (v', ω)
    -- v.j = v'.j (from h_j), v'.c = v'.c, tau α = tau v'.c = ω
    have hv'_eq : (⟨v.j, v'.c⟩ : InvVertex) = v' := by
      cases v' with
      | mk j c =>
        simp only at h_j
        rw [h_j]
    rw [hv'_eq]
    congr 1
    rw [h_ω, h_tau_eq]

/-- Completeness for zero-edges with canonical target. -/
theorem outgoingEdges_complete_zero
    (R Q : Nat) (v v' : InvVertex) (ω : Int)
    (hv'_can : v'.c < 3 ^ (R + v.j + 1))
    (hv_jQ : v.j < Q)
    (h : InvEdgeZero R v v' ω) :
    (v', ω) ∈ outgoingEdges R Q v := by
  obtain ⟨h_j, h_X, h_cong, h_ω⟩ := h
  set α := v'.c % 9 with hα_def
  set M' := 3 ^ (R + v.j + 1) with hM'_def
  have hR' : 1 ≤ R + v.j + 1 := by omega
  have hα_list : α ∈ [(1 : Nat), 2, 4, 5, 7, 8] := InX_to_list v'.c h_X
  have h_tau_eq : tau v'.c = tau α := by rw [hα_def, ← tau_mod]
  -- Note h_cong uses R + v'.j and h_j gives v'.j = v.j + 1
  have h_cong' : (3 * v.c + 1) % M' = (2 ^ tau v'.c * v'.c) % M' := by
    have hM_eq : 3 ^ (R + v'.j) = M' := by
      rw [h_j, hM'_def]; rfl
    rw [← hM_eq]; exact h_cong
  have hy : invMod2Pow (tau α) M' * (3 * v.c + 1) % M' = v'.c := by
    rw [← h_tau_eq]
    have h_inv : 2 ^ tau v'.c * invMod2 M' ^ tau v'.c ≡ 1 [MOD M'] := by
      show (2 ^ tau v'.c * invMod2 M' ^ tau v'.c) % M' = 1 % M'
      exact two_pow_mul_invMod2Pow_three_pow _ _ hR'
    have h_cong_me : 3 * v.c + 1 ≡ 2 ^ tau v'.c * v'.c [MOD M'] := h_cong'
    have h_main : invMod2Pow (tau v'.c) M' * (3 * v.c + 1) ≡ v'.c [MOD M'] := by
      unfold invMod2Pow
      have step1 : invMod2 M' ^ tau v'.c % M' * (3 * v.c + 1)
                 ≡ invMod2 M' ^ tau v'.c * (3 * v.c + 1) [MOD M'] := by
        show (invMod2 M' ^ tau v'.c % M' * (3 * v.c + 1)) % M'
           = (invMod2 M' ^ tau v'.c * (3 * v.c + 1)) % M'
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      calc invMod2 M' ^ tau v'.c % M' * (3 * v.c + 1)
          ≡ invMod2 M' ^ tau v'.c * (3 * v.c + 1) [MOD M'] := step1
        _ ≡ invMod2 M' ^ tau v'.c * (2 ^ tau v'.c * v'.c) [MOD M'] :=
              h_cong_me.mul_left _
        _ = (2 ^ tau v'.c * invMod2 M' ^ tau v'.c) * v'.c := by ring
        _ ≡ 1 * v'.c [MOD M'] := h_inv.mul_right _
        _ = v'.c := by ring
    have h_mod : (invMod2Pow (tau v'.c) M' * (3 * v.c + 1)) % M' = v'.c % M' := h_main
    rw [Nat.mod_eq_of_lt hv'_can] at h_mod
    exact h_mod
  have hy_alpha : (invMod2Pow (tau α) M' * (3 * v.c + 1) % M') % 9 = α := by
    rw [hy, ← hα_def]
  -- Show (v', ω) is in zeroEdges (second part of outgoingEdges)
  unfold outgoingEdges
  rw [List.mem_append]
  refine Or.inr ?_
  rw [if_pos hv_jQ]
  simp only [List.mem_filterMap]
  refine ⟨α, ?_, ?_⟩
  · simpa using hα_list
  · show (let τ := tau α; let y := invMod2Pow τ M' * (3 * v.c + 1) % M';
          if y % 9 = α then some (⟨v.j + 1, y⟩, (τ : Int) - 2) else none)
       = some (v', ω)
    simp only [hy_alpha, if_pos]
    rw [hy]
    have hv'_eq : (⟨v.j + 1, v'.c⟩ : InvVertex) = v' := by
      cases v' with
      | mk j c =>
        simp only at h_j
        rw [h_j]
    rw [hv'_eq]
    congr 1
    rw [h_ω, h_tau_eq]

/-! ### Edge weight lower bound -/

/-- For any admissible residue, `τ ≥ 1`. -/
theorem tau_ge_one {n : Nat} (h : InX n) : 1 ≤ tau n := by
  unfold InX at h
  unfold tau
  rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

/-- Every inverse-graph edge weight satisfies `ω ≥ v.j − v'.j`.

For `InvEdgeOne`: `v'.j = v.j` and `ω = τ ≥ 1 ≥ 0`.
For `InvEdgeZero`: `v'.j = v.j + 1` and `ω = τ − 2 ≥ −1`. -/
theorem InvEdge_weight_lower_bound
    {R : Nat} {v v' : InvVertex} {ω : Int}
    (h : InvEdge R v v' ω) :
    (v.j : Int) - (v'.j : Int) ≤ ω := by
  rcases h with h_one | h_zero
  · obtain ⟨h_j, h_X, _, h_ω⟩ := h_one
    rw [h_ω]
    have h_tau : 1 ≤ tau v'.c := tau_ge_one h_X
    have : v.j = v'.j := h_j.symm
    omega
  · obtain ⟨h_j, h_X, _, h_ω⟩ := h_zero
    rw [h_ω]
    have h_tau : 1 ≤ tau v'.c := tau_ge_one h_X
    have : v'.j = v.j + 1 := h_j
    omega

/-! ### Suffix weight bound (lemma S216.1) -/

/-- **S216.1 suffix weight bound**: for any WPath from `v` to `t` of
weight `w` where every vertex along the path (including `v`) has
`j ≤ Q`, the weight satisfies `w ≥ −(Q − v.j)`.

The argument: every negative edge in the path is a zero-edge
contributing weight `−1` and incrementing `j` by `1`. The total
descent is bounded by the number of available zero-budget steps,
which is at most `Q − v.j`. -/
theorem suffix_weight_bound
    {R : Nat} (Q : Nat)
    {v t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) v t w vs)
    (h_v_bound : v.j ≤ Q)
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q) :
    -((Q : Int) - v.j) ≤ w := by
  induction vs generalizing v w with
  | nil =>
      simp only [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      have : (v.j : Int) ≤ Q := by exact_mod_cast h_v_bound
      omega
  | cons u vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      have h_u_bound : u.j ≤ Q := h_path_bound u (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_bound : ∀ x ∈ vs', x.j ≤ Q := fun x hx =>
        h_path_bound x (List.mem_cons.mpr (Or.inr hx))
      have ih_result := ih h_rest h_u_bound h_rest_bound
      have h_ω₁ : (v.j : Int) - (u.j : Int) ≤ ω₁ :=
        InvEdge_weight_lower_bound h_edge
      have h_u_le : (u.j : Int) ≤ Q := by exact_mod_cast h_u_bound
      have h_v_le : (v.j : Int) ≤ Q := by exact_mod_cast h_v_bound
      omega

/-! ### S216 credit and relevance -/

/-- `credit Q v := Q − v.j`, the maximum number of inverse-zero-edges
that can still be used from `v`. -/
def credit (Q : Nat) (v : InvVertex) : Int := (Q : Int) - (v.j : Int)

/-- A state-cost pair `(v, d)` is *relevant* if it can still complete
to a goal at total cost `< T` using the remaining zero-budget:
`d − credit Q v < T`. -/
def relevant (Q : Nat) (T : Int) (v : InvVertex) (d : Int) : Prop :=
  d - credit Q v < T

/-- **Prefix relevance** (S216.2): if a full path from `v` to `t` has
weight `< T` and all path vertices have `j ≤ Q`, then the starting
label `(v, 0)` is relevant. -/
theorem prefix_relevant_zero
    {R : Nat} (Q : Nat) (T : Int)
    {v t : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) v t w vs)
    (h_v_bound : v.j ≤ Q)
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q)
    (h_w_lt : w < T) :
    relevant Q T v 0 := by
  unfold relevant credit
  have h_bound := suffix_weight_bound Q h_path h_v_bound h_path_bound
  linarith

/-! ### S216 certificate structure -/

/-- A computable S216 closure certificate for `(R, Q, T)`. The dist
table is a partial function `InvVertex → Option Int` over visited
states. Three invariants encode Bellman-Ford fixed-point semantics
with optimistic closure:

* `start_dist` — the start has dist `0`.
* `no_goal_lt` — no goal vertex in the table has dist `< T`.
* `closed` — for every relevant `(v, d)` and every outgoing edge to
  a *relevant* target, the target is in the table with dist `≤ d + ω`.

The `closed` invariant is the optimistic closure rule: only relevant
labels need to propagate. -/
structure S216Cert (R Q : Nat) (T : Int) where
  start : InvVertex
  dist  : InvVertex → Option Int
  /-- Start has dist `0`. -/
  start_dist : dist start = some 0
  /-- No goal vertex in the table has dist `< T`. -/
  no_goal_lt :
    ∀ v d, dist v = some d → InvVertex.IsGoal v R → ¬ d < T
  /-- Closure under outgoing edges, in the relevant region. -/
  closed :
    ∀ v d v' ω,
      dist v = some d →
      relevant Q T v d →
      InvEdge R v v' ω →
      v'.j ≤ Q →
      relevant Q T v' (d + ω) →
      ∃ d', dist v' = some d' ∧ d' ≤ d + ω

/-! ### S216 closure-to-barrier theorem (TO CLOSE)

The remaining target: given an `S216Cert R Q T` and any inverse-graph
path of weight `< T` from `cert.start` to a goal, derive `False`.

Proof outline:
1. Induct on the path.
2. At each step, maintain invariant `dist(vᵢ) = some dᵢ' ∧ dᵢ' ≤ prefix_costᵢ`.
3. Use `suffix_weight_bound` to ensure every prefix label is relevant.
4. Apply the `closed` rule to propagate dist to the next vertex.
5. At the goal, `dist(goal) ≤ w < T` contradicts `no_goal_lt`.

The induction itself is structural on `vs` with the invariant carried
generalized over the current "head". -/

/-- **Dist propagation along a path**: starting at any vertex `v_start`
with `cert.dist v_start = some d_v_start`, if the total path weight
plus `d_v_start` stays below `T`, then the endpoint `t` is also in
the dist table with value `≤ d_v_start + w`.

Proof by induction on path length, using:
* `suffix_weight_bound` (twice) to ensure the current vertex and the
  next vertex are *relevant* (so closure applies);
* `cert.closed` to propagate dist by one edge;
* IH for the remaining sub-path. -/
theorem propagate_dist
    {R Q : Nat} {T : Int} (cert : S216Cert R Q T)
    {v_start t : InvVertex} {w d_v_start : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) v_start t w vs)
    (h_v_bound : v_start.j ≤ Q)
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q)
    (h_v_dist : cert.dist v_start = some d_v_start)
    (h_total_lt : d_v_start + w < T) :
    ∃ d_t, cert.dist t = some d_t ∧ d_t ≤ d_v_start + w := by
  induction vs generalizing v_start w d_v_start with
  | nil =>
      simp only [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      exact ⟨d_v_start, h_v_dist, by linarith⟩
  | cons u vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      have h_u_bound : u.j ≤ Q :=
        h_path_bound u (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_bound : ∀ x ∈ vs', x.j ≤ Q := fun x hx =>
        h_path_bound x (List.mem_cons.mpr (Or.inr hx))
      -- Suffix bound on sub-path u → t.
      have h_suffix : -((Q : Int) - u.j) ≤ ω₂ :=
        suffix_weight_bound Q h_rest h_u_bound h_rest_bound
      -- Full suffix bound from v_start through u to t.
      have h_full_suffix : -((Q : Int) - v_start.j) ≤ ω₁ + ω₂ := by
        have h_full : WPath (InvEdge R) v_start t (ω₁ + ω₂) (u :: vs') := by
          simp only [WPath]
          exact ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩
        exact suffix_weight_bound Q h_full h_v_bound h_path_bound
      -- v_start is relevant.
      have h_v_rel : relevant Q T v_start d_v_start := by
        unfold relevant credit; linarith
      -- u is relevant at cost d_v_start + ω₁.
      have h_u_rel : relevant Q T u (d_v_start + ω₁) := by
        unfold relevant credit; linarith
      -- Apply closure: u is in dist with value ≤ d_v_start + ω₁.
      obtain ⟨d_u', h_u_dist, h_u_le⟩ :=
        cert.closed v_start d_v_start u ω₁
          h_v_dist h_v_rel h_edge h_u_bound h_u_rel
      -- Recurse on sub-path u → t.
      have h_u_total_lt : d_u' + ω₂ < T := by linarith
      obtain ⟨d_t, h_t_dist, h_t_le⟩ :=
        ih h_rest h_u_bound h_rest_bound h_u_dist h_u_total_lt
      exact ⟨d_t, h_t_dist, by linarith⟩

/-- **S216 closure-to-barrier**: any path of weight `< T` from the
certificate start to a goal vertex yields `False` (via the chain
`dist(goal) ≤ w < T` contradicting `no_goal_lt`). -/
theorem closure_to_barrier
    {R Q : Nat} {T : Int} (cert : S216Cert R Q T)
    {goal : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) cert.start goal w vs)
    (h_g : InvVertex.IsGoal goal R)
    (h_start_bound : cert.start.j ≤ Q)
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q)
    (h_w_lt : w < T) :
    False := by
  obtain ⟨d_goal, h_goal_dist, h_goal_le⟩ :=
    propagate_dist cert h_path h_start_bound h_path_bound
      cert.start_dist (by linarith)
  have h_lt : d_goal < T := by linarith
  exact cert.no_goal_lt goal d_goal h_goal_dist h_g h_lt

/-! ### Auxiliary: `j` is non-decreasing along inverse paths -/

/-- Every inverse-graph edge has `v.j ≤ v'.j` (one-edges keep `j`,
zero-edges increment it). -/
theorem InvEdge_j_monotone {R : Nat} {v v' : InvVertex} {ω : Int}
    (h : InvEdge R v v' ω) :
    v.j ≤ v'.j := by
  rcases h with h_one | h_zero
  · obtain ⟨h_j, _, _, _⟩ := h_one
    omega
  · obtain ⟨h_j, _, _, _⟩ := h_zero
    omega

/-- In any inverse-graph WPath from `v` to `t`, every vertex `u` along
the path (including `v`) satisfies `u.j ≤ t.j`. -/
theorem WPath_j_monotone
    {R : Nat} {v t : InvVertex} {w : Int} {vs : List InvVertex}
    (h : WPath (InvEdge R) v t w vs) :
    v.j ≤ t.j ∧ ∀ u ∈ vs, u.j ≤ t.j := by
  induction vs generalizing v w with
  | nil =>
      simp only [WPath] at h
      obtain ⟨rfl, _⟩ := h
      refine ⟨le_refl _, ?_⟩
      intro u hu; exact absurd hu (List.not_mem_nil)
  | cons u vs' ih =>
      simp only [WPath] at h
      obtain ⟨ω₁, ω₂, h_edge, h_rest, _⟩ := h
      obtain ⟨h_u_le, h_rest_le⟩ := ih h_rest
      refine ⟨?_, ?_⟩
      · have : v.j ≤ u.j := InvEdge_j_monotone h_edge
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_u_le
        · exact h_rest_le x hx'

/-- For any admissible word `u` and state `s`,
`(runWord u s).q = s.q + Word.numZeros u`. -/
theorem runWord_q_eq (u : Word) (s : AdmState) :
    (runWord u s).q = s.q + Word.numZeros u := by
  induction u generalizing s with
  | nil => rfl
  | cons b u' ih =>
      cases b with
      | one =>
          show (runWord u' (step s Branch.one)).q
             = s.q + Word.numZeros (Branch.one :: u')
          rw [ih, Word.numZeros_cons_one]
          rfl
      | zero =>
          show (runWord u' (step s Branch.zero)).q
             = s.q + Word.numZeros (Branch.zero :: u')
          rw [ih, Word.numZeros_cons_zero]
          show s.q + 1 + Word.numZeros u'
             = s.q + (Word.numZeros u' + 1)
          omega

/-- Corollary at `initState`: `(evalWord u).q = Word.numZeros u`. -/
theorem evalWord_q_eq (u : Word) :
    (evalWord u).q = Word.numZeros u := by
  show (runWord u initState).q = Word.numZeros u
  rw [runWord_q_eq]
  show 0 + Word.numZeros u = Word.numZeros u
  omega

/-! ### Bool-decidable form: `S216Cert_outgoing`

The `S216Cert.closed` field above quantifies over `InvEdge R v v' ω`,
which is a Prop relation — not directly Bool-decidable. The Python
engine produces certificates whose closure check iterates over
`outgoingEdges R Q v`. We provide an alternative structure
`S216Cert_outgoing` whose `closed` field uses `outgoingEdges`
directly — this IS Bool-decidable. Combined with `outgoingEdges_sound`
and `outgoingEdges_complete_one`/`_zero`, we can chain
`S216Cert_outgoing → barrier` for *canonical* paths (which is what
`S212_forward` produces). -/

/-- `S216Cert` variant where the closure check uses `outgoingEdges`
directly (decidable enumeration) rather than `InvEdge` (Prop). -/
structure S216Cert_outgoing (R Q : Nat) (T : Int) where
  start : InvVertex
  dist  : InvVertex → Option Int
  start_dist : dist start = some 0
  no_goal_lt :
    ∀ v d, dist v = some d → InvVertex.IsGoal v R → ¬ d < T
  /-- Closure over `outgoingEdges` (decidable). -/
  closed_outgoing :
    ∀ v d, dist v = some d → relevant Q T v d →
      ∀ e ∈ outgoingEdges R Q v,
        e.1.j ≤ Q →
        relevant Q T e.1 (d + e.2) →
        ∃ d', dist e.1 = some d' ∧ d' ≤ d + e.2

/-- Dist propagation along a path where the target of each edge is
canonical. Uses `outgoingEdges_complete_one`/`_zero` to translate
each `InvEdge` step into an `outgoingEdges` entry, then applies the
Bool-decidable closure. -/
theorem propagate_dist_outgoing
    {R Q : Nat} {T : Int} (cert : S216Cert_outgoing R Q T)
    {v_start t : InvVertex} {w d_v_start : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) v_start t w vs)
    (hR : 1 ≤ R)
    (h_v_can : v_start.c < 3 ^ (R + v_start.j))
    (h_path_can : ∀ u ∈ vs, u.c < 3 ^ (R + u.j))
    (h_v_bound : v_start.j ≤ Q)
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q)
    (h_v_dist : cert.dist v_start = some d_v_start)
    (h_total_lt : d_v_start + w < T) :
    ∃ d_t, cert.dist t = some d_t ∧ d_t ≤ d_v_start + w := by
  induction vs generalizing v_start w d_v_start with
  | nil =>
      simp only [WPath] at h_path
      obtain ⟨rfl, rfl⟩ := h_path
      exact ⟨d_v_start, h_v_dist, by linarith⟩
  | cons u vs' ih =>
      simp only [WPath] at h_path
      obtain ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩ := h_path
      have h_u_bound : u.j ≤ Q :=
        h_path_bound u (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_bound : ∀ x ∈ vs', x.j ≤ Q := fun x hx =>
        h_path_bound x (List.mem_cons.mpr (Or.inr hx))
      have h_u_can : u.c < 3 ^ (R + u.j) :=
        h_path_can u (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_can : ∀ x ∈ vs', x.c < 3 ^ (R + x.j) := fun x hx =>
        h_path_can x (List.mem_cons.mpr (Or.inr hx))
      have h_suffix : -((Q : Int) - u.j) ≤ ω₂ :=
        suffix_weight_bound Q h_rest h_u_bound h_rest_bound
      have h_full_suffix : -((Q : Int) - v_start.j) ≤ ω₁ + ω₂ := by
        have h_full : WPath (InvEdge R) v_start t (ω₁ + ω₂) (u :: vs') := by
          simp only [WPath]
          exact ⟨ω₁, ω₂, h_edge, h_rest, rfl⟩
        exact suffix_weight_bound Q h_full h_v_bound h_path_bound
      have h_v_rel : relevant Q T v_start d_v_start := by
        unfold relevant credit; linarith
      have h_u_rel : relevant Q T u (d_v_start + ω₁) := by
        unfold relevant credit; linarith
      -- Translate InvEdge → outgoingEdges via completeness.
      have hR_v : 1 ≤ R + v_start.j := by omega
      have h_in_outgoing : (u, ω₁) ∈ outgoingEdges R Q v_start := by
        rcases h_edge with h_one | h_zero
        · have h_u_j_eq : u.j = v_start.j := h_one.1
          have hu_can_R : u.c < 3 ^ (R + v_start.j) := by
            rw [← h_u_j_eq]; exact h_u_can
          exact outgoingEdges_complete_one R Q v_start u ω₁ hu_can_R hR_v h_one
        · have h_u_j_eq : u.j = v_start.j + 1 := h_zero.1
          have hu_can_R : u.c < 3 ^ (R + v_start.j + 1) := by
            have h_idx : R + v_start.j + 1 = R + u.j := by omega
            rw [h_idx]; exact h_u_can
          have hv_jQ : v_start.j < Q := by
            have : u.j ≤ Q := h_u_bound
            omega
          exact outgoingEdges_complete_zero R Q v_start u ω₁ hu_can_R hv_jQ h_zero
      -- Apply Bool-decidable closure.
      obtain ⟨d_u', h_u_dist, h_u_le⟩ :=
        cert.closed_outgoing v_start d_v_start h_v_dist h_v_rel
          (u, ω₁) h_in_outgoing h_u_bound h_u_rel
      -- Recurse.
      have h_u_total_lt : d_u' + ω₂ < T := by linarith
      obtain ⟨d_t, h_t_dist, h_t_le⟩ :=
        ih h_rest h_u_can h_rest_can h_u_bound h_rest_bound h_u_dist h_u_total_lt
      exact ⟨d_t, h_t_dist, by linarith⟩

/-- **S216 closure-to-barrier (Bool-decidable form)**: any canonical
path of weight `< T` from the certificate start to a goal yields
`False`. -/
theorem closure_to_barrier_outgoing
    {R Q : Nat} {T : Int} (cert : S216Cert_outgoing R Q T)
    (hR : 1 ≤ R)
    (h_start_can : cert.start.c < 3 ^ (R + cert.start.j))
    {goal : InvVertex} {w : Int} {vs : List InvVertex}
    (h_path : WPath (InvEdge R) cert.start goal w vs)
    (h_g : InvVertex.IsGoal goal R)
    (h_start_bound : cert.start.j ≤ Q)
    (h_path_can : ∀ u ∈ vs, u.c < 3 ^ (R + u.j))
    (h_path_bound : ∀ u ∈ vs, u.j ≤ Q)
    (h_w_lt : w < T) :
    False := by
  obtain ⟨d_goal, h_goal_dist, h_goal_le⟩ :=
    propagate_dist_outgoing cert h_path hR h_start_can h_path_can
      h_start_bound h_path_bound cert.start_dist (by linarith)
  have h_lt : d_goal < T := by linarith
  exact cert.no_goal_lt goal d_goal h_goal_dist h_g h_lt

/-! ### Specialization: S216 barrier for admissible words

If the closure_to_barrier conjecture holds for an S216 certificate
at base precision `R = 22m + 2`, and word `u` has `q(u) ≤ Q` with
`n(u) ≡ aS202 (mod 3^R)`, then `T ≤ defect(u)`.

Combines `S212_forward` (Word → WPath) with the S216 closure-to-barrier. -/

/-- **Cylinder barrier for words from an S216 certificate** (modulo
the open `closure_to_barrier` step). The hypothesis `h_S216` is what
remains to be formalized; once closed, this gives a *fully Lean
verified* `𝒞^←_{S202}(m, Q) ≥ T` whenever the engine produces a
verified certificate. -/
theorem S216_barrier_for_words
    {m Q : Nat} {T : Int}
    (cert : S216Cert (22 * m + 2) Q T)
    (h_start_match : cert.start = InvStart m)
    (u : Word)
    (h_q_bound : (evalWord u).q ≤ Q)
    (h_cyl : (evalWord u).n % (3 ^ (22 * m + 2))
              = aS202 % (3 ^ (22 * m + 2))) :
    T ≤ defect (evalWord u) := by
  by_contra h_not_le
  have h_lt : defect (evalWord u) < T := not_le.mp h_not_le
  obtain ⟨vs, goal, h_g, h_goal_j, _h_can, h_path⟩ := S212_forward m u h_cyl
  -- (evalWord u).q = Word.numZeros u, hence numZeros u ≤ Q.
  have h_numZeros_le : Word.numZeros u ≤ Q := by
    rw [← evalWord_q_eq]; exact h_q_bound
  -- goal.j = Word.numZeros u, hence goal.j ≤ Q.
  have h_goal_j_le : goal.j ≤ Q := by rw [h_goal_j]; exact h_numZeros_le
  -- By WPath_j_monotone, every vertex in vs has j ≤ goal.j ≤ Q.
  have h_mono := WPath_j_monotone h_path
  have h_start_le : (InvStart m).j ≤ goal.j := h_mono.1
  have h_vs_le : ∀ u ∈ vs, u.j ≤ Q := fun u hu => by
    have := h_mono.2 u hu
    omega
  -- Translate to cert.start.
  rw [← h_start_match] at h_path h_start_le
  -- cert.start.j ≤ Q.
  have h_cert_start_le : cert.start.j ≤ Q := by omega
  -- Apply closure_to_barrier.
  exact closure_to_barrier cert h_path h_g h_cert_start_le h_vs_le h_lt

/-! ### Bool-decidable form chain: Word → S216Cert_outgoing → Barrier

This is the formal pipeline a Python-generated certificate plugs into.
The `S216Cert_outgoing` has Bool-decidable fields (verifiable via
`native_decide`), and combined with `outgoingEdges_complete_*` and
the canonicality of `S212_forward` paths, it closes the chain. -/

/-- **End-to-end barrier from a Bool-decidable certificate**: given a
`S216Cert_outgoing` whose start matches `InvStart m` and a Word `u`
with `q(u) ≤ Q` in the m-th cylinder, conclude `T ≤ defect(u)`. -/
theorem S216_barrier_for_words_outgoing
    {m Q : Nat} {T : Int}
    (cert : S216Cert_outgoing (22 * m + 2) Q T)
    (h_start_match : cert.start = InvStart m)
    (h_start_can : cert.start.c < 3 ^ (22 * m + 2 + cert.start.j))
    (u : Word)
    (h_q_bound : (evalWord u).q ≤ Q)
    (h_cyl : (evalWord u).n % (3 ^ (22 * m + 2))
              = aS202 % (3 ^ (22 * m + 2))) :
    T ≤ defect (evalWord u) := by
  by_contra h_not_le
  have h_lt : defect (evalWord u) < T := not_le.mp h_not_le
  obtain ⟨vs, goal, h_g, h_goal_j, h_can, h_path⟩ := S212_forward m u h_cyl
  have h_numZeros_le : Word.numZeros u ≤ Q := by
    rw [← evalWord_q_eq]; exact h_q_bound
  have h_goal_j_le : goal.j ≤ Q := by rw [h_goal_j]; exact h_numZeros_le
  have h_mono := WPath_j_monotone h_path
  have h_vs_le : ∀ u ∈ vs, u.j ≤ Q := fun u hu => by
    have := h_mono.2 u hu; omega
  have h_cert_start_le : cert.start.j ≤ Q := by
    rw [h_start_match]
    show 0 ≤ Q
    omega
  rw [← h_start_match] at h_path
  exact closure_to_barrier_outgoing cert (by omega) h_start_can
    h_path h_g h_cert_start_le h_can h_vs_le h_lt

/-! ### Named Prop aliases for the three certificate fields

These are the same as the three fields of `S216Cert_outgoing` but
exposed as standalone `def`s, matching the conceptual taxonomy of the
S216 paper (and required by the cert-generator pipeline). -/

/-- **`S216StartOK start dist`** — the certificate's `dist` table assigns
distance `0` to the start vertex. -/
def S216StartOK (start : InvVertex) (dist : InvVertex → Option Int) : Prop :=
  dist start = some 0

/-- **`S216NoGoalBelowT R T dist`** — no goal vertex in the `dist`
table has distance strictly below the threshold `T`. -/
def S216NoGoalBelowT (R : Nat) (T : Int) (dist : InvVertex → Option Int) : Prop :=
  ∀ v d, dist v = some d → InvVertex.IsGoal v R → ¬ d < T

/-- **`S216OptimisticClosed R Q T dist`** — for every relevant `(v, d)`
in `dist` and every outgoing edge of `v` whose target is also relevant,
the target's `dist` is at most `d + ω` (the propagated value). The
"optimistic" qualifier is the credit-based relevance rule
`relevant Q T v d := d - (Q - v.j) < T`. -/
def S216OptimisticClosed (R Q : Nat) (T : Int)
    (dist : InvVertex → Option Int) : Prop :=
  ∀ v d, dist v = some d → relevant Q T v d →
    ∀ e ∈ outgoingEdges R Q v,
      e.1.j ≤ Q →
      relevant Q T e.1 (d + e.2) →
      ∃ d', dist e.1 = some d' ∧ d' ≤ d + e.2

/-- **Named-Prop constructor for `S216Cert_outgoing`**: the named Prop
aliases above are precisely the three soundness invariants of the
structure. -/
def S216Cert_outgoing.mk' {R Q : Nat} {T : Int}
    (start : InvVertex) (dist : InvVertex → Option Int)
    (h_start : S216StartOK start dist)
    (h_no_goal : S216NoGoalBelowT R T dist)
    (h_closed : S216OptimisticClosed R Q T dist) :
    S216Cert_outgoing R Q T :=
  { start := start
  , dist := dist
  , start_dist := h_start
  , no_goal_lt := h_no_goal
  , closed_outgoing := h_closed }

/-! ### Named alias for terminal barrier statements

`S216BarrierForWords m Q T` is the standard statement of the cylinder
accessibility lower bound: every admissible word landing in the m-th
S202 cylinder with at most Q zero-steps has defect at least T.
Equivalent to `𝒞^←_{S202}(m, Q) ≥ T`. -/
def S216BarrierForWords (m Q : Nat) (T : Int) : Prop :=
  ∀ u : Word,
    (evalWord u).q ≤ Q →
    (evalWord u).n % (3 ^ (22 * m + 2)) = aS202 % (3 ^ (22 * m + 2)) →
    T ≤ defect (evalWord u)

end CollatzLean4.Admissible
