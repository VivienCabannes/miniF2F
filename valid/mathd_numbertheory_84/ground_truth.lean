import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_84 : Int.floor ((9 : ℝ) / 160 * 100) = 5 := by
  have decimal_eq : (9 : ℝ) / 160 = 0.05625 := by
    norm_num
    -- This tactic normalizes the numerical expression to verify the decimal representation of 9/160.
    <;> norm_num
    -- This tactic is used to ensure all numerical expressions are in their normal form, confirming the accuracy of the decimal representation.
    <;> norm_num
    <;> norm_num
    <;> norm_num
  
  have shifted_decimal : (9 : ℝ) / 160 * 100 = 5.625 := by
    norm_num [decimal_eq]
    <;> norm_num
    <;> norm_num
    <;> norm_num
    <;> norm_num
  
  have floor_value : Int.floor ((9 : ℝ) / 160 * 100) = 5 := by
    norm_num [Int.floor_eq_iff, shifted_decimal]
    <;> norm_num
    <;> linarith
  
  -- Given that the floor of the shifted decimal is 5, we directly use this fact to conclude the proof.
  simpa [shifted_decimal, floor_value] using floor_value