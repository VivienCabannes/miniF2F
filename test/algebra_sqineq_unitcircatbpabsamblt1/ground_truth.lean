import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  have h₁ : a ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg b]
    <;> nlinarith
  
  have h₂ : a ≥ -1 := by
    nlinarith [sq_nonneg (a + 1), sq_nonneg b]
  
  have h₃ : b ≤ 1 := by
    nlinarith [sq_nonneg (b - 1), sq_nonneg a]
  
  have h₄ : b ≥ -1 := by
    nlinarith [sq_nonneg (b + 1), sq_nonneg a]
  
  have h₅ : a ≥ b → a * b + abs (a - b) ≤ 1 := by
    intro h₅
    have h₅₁ : abs (a - b) = a - b := by
      rw [abs_of_nonneg (sub_nonneg.mpr h₅)]
    rw [h₅₁]
    have h₅₂ : a * b + (a - b) ≤ 1 := by
      have h₅₃ : (a - 1) * (b + 1) ≤ 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1)]
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1)]
    linarith
  
  have h₆ : a < b → a * b + abs (a - b) ≤ 1 := by
    intro h₆
    have h₆₁ : abs (a - b) = b - a := by
      rw [abs_of_neg (by linarith)]
      <;> linarith
    rw [h₆₁]
    have h₆₂ : a * b + (b - a) ≤ 1 := by
      have h₆₃ : (a + 1) * (b - 1) ≤ 0 := by
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 1)]
      nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 1)]
    linarith
  
  have h₇ : a * b + abs (a - b) ≤ 1 := by
    by_cases h₇ : a ≥ b
    · -- Case: a ≥ b
      exact h₅ h₇
    · -- Case: a < b
      have h₇₁ : a < b := by
        by_contra h₇₁
        -- If a ≥ b is false, then a < b must be true
        have h₇₂ : a ≥ b := by linarith
        contradiction
      exact h₆ h₇₁
  
  exact h₇