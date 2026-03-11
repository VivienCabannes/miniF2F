import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  have h₀ : a * (2 - a) = 2 * a - a ^ 2 := by
    ring_nf
    <;>
    linarith
  
  have h₁ : (a - 1) ^ 2 ≥ 0 := by
    -- Use the fact that the square of any real number is non-negative.
    nlinarith [sq_nonneg (a - 1)]
  
  have h₂ : a * (2 - a) ≤ 1 := by
    have h₃ : 2 * a - a ^ 2 ≤ 1 := by
      -- Use the non-negativity of (a - 1)^2 to prove the inequality.
      nlinarith [sq_nonneg (a - 1)]
    -- Use the previously derived inequality to conclude the proof.
    linarith
  
  exact h₂