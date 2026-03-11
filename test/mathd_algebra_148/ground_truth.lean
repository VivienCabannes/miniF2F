import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_148
  (c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = c * x^3 - 9 * x + 3)
  (h₁ : f 2 = 9) :
  c = 3 := by
  have h₂ : c * (2 : ℝ) ^ 3 - 9 * (2 : ℝ) + 3 = 9 := by
    have h₂₁ : f 2 = c * (2 : ℝ) ^ 3 - 9 * (2 : ℝ) + 3 := by
      rw [h₀]
      <;> norm_num
    rw [h₂₁] at h₁
    linarith
  
  have h₃ : c * 8 - 18 + 3 = 9 := by
    norm_num at h₂ ⊢
    <;> linarith
  
  have h₄ : c * 8 - 15 = 9 := by
    norm_num at h₃ ⊢
    <;> linarith
  
  have h₅ : c * 8 = 24 := by
    have h₅₁ : c * 8 - 15 = 9 := h₄
    have h₅₂ : c * 8 = 24 := by linarith
    exact h₅₂
  
  have h₆ : c = 3 := by
    have h₆₁ : c * 8 = 24 := h₅
    have h₆₂ : c = 3 := by
      apply mul_left_cancel₀ (show (8 : ℝ) ≠ 0 by norm_num)
      linarith
    exact h₆₂
  
  apply h₆