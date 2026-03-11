import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2013_p4 :
  (2^2014 + 2^2012) / (2^2014 - 2^2012) = (5:ℝ) / 3 := by
  have h₀ : (2 : ℝ) ^ 2014 - (2 : ℝ) ^ 2012 > 0 := by
    have h₁ : (2 : ℝ) ^ 2014 > (2 : ℝ) ^ 2012 := by
      -- Prove that 2^2014 > 2^2012 using the fact that the exponential function with base > 1 is increasing.
      apply pow_lt_pow_right (by norm_num)
      <;> norm_num
    -- Since 2^2014 > 2^2012, their difference is positive.
    linarith
  
  have h₁ : ((2 : ℝ) ^ 2014 + (2 : ℝ) ^ 2012) / ((2 : ℝ) ^ 2014 - (2 : ℝ) ^ 2012) = (5 : ℝ) / 3 := by
    have h₂ : (2 : ℝ) ^ 2014 = 4 * (2 : ℝ) ^ 2012 := by
      ring_nf
      <;> norm_num [pow_add, pow_mul, mul_assoc]
      <;>
      linarith
    rw [h₂]
    have h₃ : (4 * (2 : ℝ) ^ 2012 + (2 : ℝ) ^ 2012 : ℝ) = 5 * (2 : ℝ) ^ 2012 := by
      ring_nf
      <;>
      linarith
    have h₄ : (4 * (2 : ℝ) ^ 2012 - (2 : ℝ) ^ 2012 : ℝ) = 3 * (2 : ℝ) ^ 2012 := by
      ring_nf
      <;>
      linarith
    rw [h₃, h₄]
    have h₅ : (5 * (2 : ℝ) ^ 2012 : ℝ) / (3 * (2 : ℝ) ^ 2012 : ℝ) = (5 : ℝ) / 3 := by
      have h₆ : (2 : ℝ) ^ 2012 ≠ 0 := by positivity
      field_simp [h₆]
      <;>
      ring_nf
      <;>
      linarith
    rw [h₅]
    <;>
    ring_nf
    <;>
    linarith
  
  have h₂ : (2 ^ 2014 + 2 ^ 2012 : ℝ) / (2 ^ 2014 - 2 ^ 2012 : ℝ) = (5 : ℝ) / 3 := by
    norm_num [pow_succ, add_assoc, mul_assoc, mul_comm, mul_left_comm] at h₁ ⊢
    <;>
    ring_nf at h₁ ⊢ <;>
    simpa using h₁
  
  have h₃ : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
    norm_num [h₂] at *
    <;>
    simpa using h₂
  
  apply h₃