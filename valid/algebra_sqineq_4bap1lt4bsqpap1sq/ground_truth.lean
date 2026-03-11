import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_4bap1lt4bsqpap1sq (a b : ℝ) : 4 * b * (a + 1) ≤ 4 * b ^ 2 + (a + 1) ^ 2 := by
  have step1 : 4 * b * (a + 1) - 4 * b^2 - (a + 1)^2 ≤ 0 := by
    -- Use nlinarith to handle the inequality by leveraging non-linear arithmetic
    nlinarith [sq_nonneg (a - 2 * b + 1), sq_nonneg (a - 2 * b), sq_nonneg (a + 1 - 2 * b), sq_nonneg (a + 1), sq_nonneg (2 * b)]
  
  have step2 : - ( (2 * b - (a + 1)) ^ 2 ) ≤ 0 := by
    -- Use the fact that the square of any real number is non-negative to establish the inequality.
    linarith [sq_nonneg (2 * b - (a + 1))]
    -- The above line uses the fact that -(x^2) ≤ 0 for all real x, which is true because x^2 ≥ 0.
    <;> linarith
    <;> linarith
    <;> linarith
  
  have step3 : (2 * b - (a + 1)) ^ 2 ≥ 0 := by
    -- Use the fact that the square of any real number is non-negative to conclude the proof.
    nlinarith [sq_nonneg (2 * b - (a + 1))]
  
  have final : 4 * b * (a + 1) ≤ 4 * b^2 + (a + 1)^2 := by
    -- Using the fact that the square of any real number is non-negative, we can directly conclude the inequality.
    linarith [sq_nonneg (2 * b - (a + 1))]
    -- The `linarith` tactic is used to solve linear arithmetic problems, and it uses the non-negativity of the square term to prove the inequality.
    <;> linarith
    -- This line ensures that all inequalities are checked and the proof is complete.
    <;> linarith
  
  linarith