import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1990_p2 :
  (52 + 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) - (52 - 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) = 828 := by
  have h1 : 52 + 6 * Real.sqrt 43 = (Real.sqrt 43 + 3)^2 := by
    have h : 0 ≤ Real.sqrt 43 := Real.sqrt_nonneg _
    -- Use the fact that the square root of 43 is non-negative to ensure the square root is non-negative.
    have h2 : 0 ≤ 3 := by norm_num
    -- Verify that 3 is non-negative, which is trivially true.
    have h3 : 0 ≤ Real.sqrt 43 * 3 := by positivity
    -- Confirm that the product of a non-negative number and 3 is non-negative.
    have h4 : 0 ≤ Real.sqrt 43 * Real.sqrt 43 := by positivity
    -- Confirm that the product of two non-negative numbers is non-negative.
    nlinarith [Real.sq_sqrt (show 0 ≤ 43 by norm_num), sq_nonneg (Real.sqrt 43 - 3)]
  
  have h2 : 52 - 6 * Real.sqrt 43 = (Real.sqrt 43 - 3)^2 := by
    have h2 : 0 ≤ Real.sqrt 43 := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (Real.sqrt 43 - 3), sq_nonneg (Real.sqrt 43 + 3),
      Real.sq_sqrt (show 0 ≤ 43 by norm_num)]
  
  have h3 : (52 + 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) = (Real.sqrt 43 + 3)^3 := by
    have h3 : 0 < Real.sqrt 43 := by
      apply Real.sqrt_pos_of_pos
      norm_num
    have h4 : 0 < Real.sqrt 43 + 3 := by
      nlinarith [h3]
    have h5 : 0 < Real.sqrt 43 - 3 := by
      nlinarith [h3]
    -- Use the properties of exponents and logarithms to prove the equality.
    rw [← Real.rpow_nat_cast]
    simp_all [Real.rpow_def_of_pos, mul_comm]
    <;> ring_nf
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ 43 by norm_num)]
  
  have h4 : (52 - 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) = (Real.sqrt 43 - 3)^3 := by
    have h4 : 0 < Real.sqrt 43 := Real.sqrt_pos.mpr (by norm_num)
    have h5 : 0 < Real.sqrt 43 + 3 := by linarith
    have h6 : 0 < Real.sqrt 43 - 3 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 43 by norm_num)]
    -- We need to show that the expressions are equal after raising both sides to the power of 3/2.
    -- We use the properties of exponents and the fact that both expressions are positive.
    rw [← Real.rpow_nat_cast] at h3 ⊢
    simp_all [Real.rpow_def_of_pos]
    <;> ring_nf
    <;> field_simp [h4.ne', h5.ne', h6.ne'] at h3 ⊢
    <;> norm_num at h3 ⊢
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ 43 by norm_num), Real.sq_sqrt (show 0 ≤ 43 by norm_num)]
  
  have h5 : (Real.sqrt 43 + 3)^3 - (Real.sqrt 43 - 3)^3 = 828 := by
    have h5 : 0 < Real.sqrt 43 := Real.sqrt_pos.mpr (by norm_num)
    have h6 : (Real.sqrt 43) ^ 2 = 43 := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 43 - 3), sq_nonneg (Real.sqrt 43 + 3)]
  
  have h6 : (52 + 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) - (52 - 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) = 828 := by
    simp_all [pow_two, mul_add, mul_comm, mul_left_comm]
    <;> linarith
  
  linarith [h5]
  -- Using the previously derived result h5, we directly conclude the proof.
  <;> norm_num
  <;> linarith