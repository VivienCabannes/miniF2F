import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_263
  (y : ℝ)
  (h₀ : 0 ≤ 19 + 3 * y)
  (h₁ : Real.sqrt (19 + 3 * y) = 7) :
  y = 10 := by
  have h₂ : 19 + 3 * y = 49 := by
    have h₂₁ : (Real.sqrt (19 + 3 * y)) ^ 2 = 7 ^ 2 := by
      rw [h₁]
    -- Use the property that the square of the square root of a non-negative number is the number itself
    have h₂₂ : (Real.sqrt (19 + 3 * y)) ^ 2 = 19 + 3 * y := by
      rw [Real.sq_sqrt] <;> linarith
    -- Substitute back to get the equation 19 + 3 * y = 49
    linarith
  
  have h₃ : y = 10 := by
    have h₄ : 3 * y = 30 := by linarith
    have h₅ : y = 10 := by linarith
    exact h₅
  
  apply h₃