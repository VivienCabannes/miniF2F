import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_484 :
  Real.log 27 / Real.log 3 = 3 := by
  have h₀ : Real.log 27 = 3 * Real.log 3 := by
    have h₀₁ : Real.log 27 = Real.log (3 ^ 3) := by norm_num
    rw [h₀₁]
    -- Use the logarithm power rule to simplify the expression
    have h₀₂ : Real.log (3 ^ 3) = 3 * Real.log 3 := by
      rw [Real.log_pow] <;> norm_num
      <;>
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
    rw [h₀₂]
    <;>
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  
  have h₁ : Real.log 27 / Real.log 3 = 3 := by
    rw [h₀]
    have h₂ : Real.log 3 ≠ 0 := by
      -- Prove that the natural logarithm of 3 is not zero
      have h₂₁ : Real.log 3 > 0 := Real.log_pos (by norm_num)
      linarith
    -- Simplify the expression using field operations
    field_simp [h₂]
    <;> ring
    <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  
  apply h₁