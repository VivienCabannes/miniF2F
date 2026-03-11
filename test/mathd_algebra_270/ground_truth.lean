import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_270
  (f : ℝ → ℝ)
  (h₀ : ∀ x, x ≠ -2 -> f x = 1 / (x + 2)) :
  f (f 1) = 3/7 := by
  have h₁ : f 1 = 1 / 3 := by
    have h₁₁ : (1 : ℝ) ≠ -2 := by norm_num
    have h₁₂ : f 1 = 1 / (1 + 2 : ℝ) := h₀ 1 h₁₁
    rw [h₁₂]
    <;> norm_num
    <;> field_simp
    <;> ring
    <;> norm_num
  
  have h₂ : f (f 1) = f (1 / 3) := by
    rw [h₁]
    <;> norm_num
  
  have h₃ : f (1 / 3) = 3 / 7 := by
    have h₃₁ : (1 / 3 : ℝ) ≠ -2 := by norm_num
    have h₃₂ : f (1 / 3 : ℝ) = 1 / ((1 / 3 : ℝ) + 2 : ℝ) := h₀ (1 / 3 : ℝ) h₃₁
    rw [h₃₂]
    <;> norm_num
    <;> field_simp
    <;> ring
    <;> norm_num
  
  have h₄ : f (f 1) = 3 / 7 := by
    rw [h₂, h₃]
    <;> norm_num
  
  exact h₄