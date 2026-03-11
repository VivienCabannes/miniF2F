import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2020_p2 :
  ((100 ^ 2 - 7 ^ 2):ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1 := by
  have h1 : (100 : ℝ) ^ 2 - 7 ^ 2 = (100 - 7) * (100 + 7) := by
    norm_num [sub_mul, add_mul, mul_sub, mul_add, mul_one, mul_assoc]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have h2 : (70 : ℝ) ^ 2 - 11 ^ 2 = (70 - 11) * (70 + 11) := by
    norm_num [sub_mul, add_mul, mul_sub, mul_add, mul_one, mul_assoc]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have h3 : (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1 := by
    rw [h1, h2]
    have h4 : (70 - 11 : ℝ) ≠ 0 := by norm_num
    have h5 : (70 + 11 : ℝ) ≠ 0 := by norm_num
    have h6 : (100 - 7 : ℝ) ≠ 0 := by norm_num
    have h7 : (100 + 7 : ℝ) ≠ 0 := by norm_num
    field_simp [h4, h5, h6, h7]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  exact h3