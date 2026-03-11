import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_196
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ abs (2 - x) = 3) :
  ∑ k ∈ S, k = 4 := by
  have h₁ : S = { -1, 5 } := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · -- Prove the forward direction: if |2 - x| = 3, then x = -1 or x = 5
      intro h
      have h₂ : abs (2 - x) = 3 := h
      have h₃ : 2 - x = 3 ∨ 2 - x = -3 := by
        apply eq_or_eq_neg_of_abs_eq
        <;> linarith
      cases h₃ with
      | inl h₃ =>
        -- Case: 2 - x = 3
        have h₄ : x = -1 := by linarith
        rw [h₄]
        norm_num
      | inr h₃ =>
        -- Case: 2 - x = -3
        have h₄ : x = 5 := by linarith
        rw [h₄]
        norm_num
    · -- Prove the backward direction: if x = -1 or x = 5, then |2 - x| = 3
      intro h
      cases h with
      | inl h =>
        -- Case: x = -1
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
      | inr h =>
        -- Case: x = 5
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
  
  have h₂ : (∑ k in S, k) = 4 := by
    rw [h₁]
    norm_num [Finset.sum_pair (show (-1 : ℝ) ≠ 5 by norm_num)]
    <;>
    simp_all [Finset.sum_singleton]
    <;>
    norm_num
    <;>
    linarith
  
  exact h₂