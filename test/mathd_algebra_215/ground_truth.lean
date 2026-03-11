import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_215
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ (x + 3)^2 = 121) :
  ∑ k ∈ S, k = -6 := by
  have h₁ : S = ({8, -14} : Finset ℝ) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · intro h
      have h₂ : (x + 3) ^ 2 = 121 := by exact h
      have h₃ : x + 3 = 11 ∨ x + 3 = -11 := by
        apply or_iff_not_imp_left.mpr
        intro h₄
        apply eq_of_sub_eq_zero
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₄)
        nlinarith
      cases h₃ with
      | inl h₃ =>
        have h₄ : x = 8 := by linarith
        rw [h₄]
        norm_num
      | inr h₃ =>
        have h₄ : x = -14 := by linarith
        rw [h₄]
        norm_num
    · intro h
      cases h with
      | inl h =>
        rw [h]
        norm_num
      | inr h =>
        rw [h]
        norm_num
  
  have h₂ : (∑ k in S, k) = -6 := by
    rw [h₁]
    norm_num [Finset.sum_pair (show (8 : ℝ) ≠ -14 by norm_num)]
    <;>
    simp_all [Finset.sum_singleton]
    <;>
    norm_num
    <;>
    linarith
  
  apply h₂