import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_208 :
  Real.sqrt 1000000 - 1000000^(1/3) = 900 := by
  have h_sqrt : Real.sqrt 1000000 = 1000 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;>
    linarith
  
  have h_cbrt : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 100 := by
    have h₁ : Real.log ((1000000 : ℝ) ^ ((1 : ℝ) / 3)) = Real.log (100 : ℝ) := by
      have h₂ : Real.log ((1000000 : ℝ) ^ ((1 : ℝ) / 3)) = ((1 : ℝ) / 3) * Real.log (1000000 : ℝ) := by
        rw [Real.log_rpow (by norm_num : (1000000 : ℝ) > 0)]
        <;> ring_nf
      rw [h₂]
      have h₃ : Real.log (1000000 : ℝ) = Real.log ((100 : ℝ) ^ 3) := by norm_num
      rw [h₃]
      have h₄ : Real.log ((100 : ℝ) ^ 3) = 3 * Real.log (100 : ℝ) := by
        rw [Real.log_pow] <;> norm_num
      rw [h₄]
      ring_nf
      <;>
      field_simp [Real.log_mul, Real.log_pow] <;>
      ring_nf <;>
      norm_num
    have h₂ : (1000000 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
    have h₃ : (100 : ℝ) > 0 := by norm_num
    have h₄ : Real.log ((1000000 : ℝ) ^ ((1 : ℝ) / 3)) = Real.log (100 : ℝ) := by rw [h₁]
    have h₅ : Real.log ((1000000 : ℝ) ^ ((1 : ℝ) / 3)) = Real.log (100 : ℝ) := by rw [h₁]
    have h₆ : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 100 := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h₂) (Set.mem_Ioi.mpr h₃)
      linarith
    rw [h₆]
    <;>
    norm_num
  
  have h_main : Real.sqrt 1000000 - (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 900 := by
    rw [h_sqrt, h_cbrt]
    <;> norm_num
  
  rw [h_main]
  <;>
  norm_num