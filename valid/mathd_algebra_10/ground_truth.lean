import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_10 : abs ((120 : ℝ) / 100 * 30 - 130 / 100 * 20) = 10 := by
  have step1 : (120 : ℝ) / 100 * 30 = 36 := by
    norm_num
    <;> ring
    <;> norm_num
    <;> ring
    <;> norm_num
  
  have step2 : (130 : ℝ) / 100 * 20 = 26 := by
    norm_num [mul_assoc]
    <;> linarith
  
  have step3 : (120 : ℝ) / 100 * 30 - 130 / 100 * 20 = 10 := by
    -- We use the given equations to simplify and solve the expression.
    nlinarith [step1, step2]
    <;> norm_num
    <;> linarith
    <;> norm_num
    <;> linarith
  
  have step4 : |((120 : ℝ) / 100 * 30 - 130 / 100 * 20)| = 10 := by
    -- Substitute the value of the expression from step3 into the absolute value function.
    rw [step3]
    -- Simplify the absolute value of a number, which is already positive.
    <;> simp [abs_of_pos]
    -- Normalize the numerical value to ensure it is correct.
    <;> norm_num
  
  -- Use the given information to simplify the proof
  simpa [abs_of_pos] using step4