import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by
  have h₁ : a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg b]
  
  have h₂ : b ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg a]
  
  have h₃ : 1 - a ≥ 0 := by
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - 1), sq_nonneg (b - 1)]
  
  have h₄ : 1 + b ≥ 0 := by
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - 1), sq_nonneg (b + 1)]
  
  have h₅ : (1 - a) * (1 + b) ≥ 0 := by
    nlinarith [h₃, h₄]
  
  have h₆ : a * b + (a - b) ≤ 1 := by
    have h₇ : (1 - a) * (1 + b) = 1 - a + b - a * b := by
      ring
    have h₈ : 1 - a + b - a * b ≥ 0 := by
      nlinarith [h₅, h₇]
    nlinarith [h₈]
  
  exact h₆