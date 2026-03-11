import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2021_p18
  (f : ℚ → ℝ)
  (h₀ : ∀x>0, ∀y>0, f (x * y) = f x + f y)
  (h₁ : ∀p, Nat.Prime p → f p = p) :
  f (25 / 11) < 0 := by
  have h₂ : f 1 = 0 := by
    have h₂₁ : f (1 * 1 : ℚ) = f 1 + f 1 := by
      have h₂₂ : f (1 * 1 : ℚ) = f 1 + f 1 := h₀ 1 (by norm_num) 1 (by norm_num)
      exact h₂₂
    have h₂₂ : f (1 * 1 : ℚ) = f 1 + f 1 := h₂₁
    have h₂₃ : f (1 * 1 : ℚ) = f 1 := by norm_num
    have h₂₄ : f 1 + f 1 = f 1 := by linarith
    have h₂₅ : f 1 = 0 := by linarith
    exact h₂₅
  
  have h₃ : f (5 : ℚ) = (5 : ℝ) := by
    have h₃₁ : Nat.Prime 5 := by decide
    have h₃₂ : f (5 : ℚ) = (5 : ℝ) := by
      have h₃₃ : f (5 : ℚ) = 5 := h₁ 5 h₃₁
      norm_num at h₃₃ ⊢
      <;> simp_all [h₃₃]
      <;> norm_num
      <;> linarith
    exact h₃₂
  
  have h₄ : f (25 : ℚ) = (10 : ℝ) := by
    have h₄₁ : f (25 : ℚ) = f (5 * 5 : ℚ) := by norm_num
    rw [h₄₁]
    have h₄₂ : f (5 * 5 : ℚ) = f (5 : ℚ) + f (5 : ℚ) := h₀ 5 (by norm_num) 5 (by norm_num)
    rw [h₄₂]
    norm_num [h₃]
    <;> linarith
  
  have h₅ : f (11 : ℚ) = (11 : ℝ) := by
    have h₅₁ : Nat.Prime 11 := by decide
    have h₅₂ : f (11 : ℚ) = (11 : ℝ) := by
      have h₅₃ : f (11 : ℚ) = 11 := h₁ 11 h₅₁
      norm_num at h₅₃ ⊢
      <;> simp_all [h₅₃]
      <;> norm_num
      <;> linarith
    exact h₅₂
  
  have h₆ : f (25 / 11 : ℚ) = (-1 : ℝ) := by
    have h₆₁ : f ((25 / 11 : ℚ) * 11) = f (25 / 11 : ℚ) + f (11 : ℚ) := h₀ (25 / 11 : ℚ) (by norm_num) 11 (by norm_num)
    have h₆₂ : f ((25 / 11 : ℚ) * 11) = f (25 : ℚ) := by norm_num
    have h₆₃ : f (25 / 11 : ℚ) + f (11 : ℚ) = f (25 : ℚ) := by linarith
    have h₆₄ : f (25 / 11 : ℚ) = f (25 : ℚ) - f (11 : ℚ) := by linarith
    rw [h₆₄, h₄, h₅]
    <;> norm_num
    <;> linarith
  
  have h₇ : f (25 / 11 : ℚ) < 0 := by
    rw [h₆]
    <;> norm_num
    <;> linarith
  
  exact h₇