import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2020_p13 :
  Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  have h₁ : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 := by
    have h₁₁ : Real.log 6 = Real.log 2 + Real.log 3 := by
      have h₁₁₁ : Real.log 6 = Real.log (2 * 3) := by norm_num
      rw [h₁₁₁]
      have h₁₁₂ : Real.log (2 * 3) = Real.log 2 + Real.log 3 := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      rw [h₁₁₂]
    have h₁₂ : Real.log 6 / Real.log 2 = 1 + Real.log 3 / Real.log 2 := by
      rw [h₁₁]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
      <;> ring_nf
      <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
      <;> ring_nf
    have h₁₃ : Real.log 6 / Real.log 3 = 1 + Real.log 2 / Real.log 3 := by
      rw [h₁₁]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
      <;> ring_nf
      <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
      <;> ring_nf
    rw [h₁₂, h₁₃]
    <;> ring_nf
    <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
    <;> ring_nf
    <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
    <;> ring_nf
  
  have h₂ : Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt ((Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2) := by
    rw [h₁]
    <;>
    simp [Real.sqrt_eq_iff_sq_eq]
    <;>
    ring_nf
    <;>
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
    <;>
    ring_nf
    <;>
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
    <;>
    ring_nf
  
  have h₃ : Real.sqrt ((Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
    have h₃₁ : Real.log 3 / Real.log 2 > 0 := by
      apply div_pos
      · exact Real.log_pos (by norm_num)
      · exact Real.log_pos (by norm_num)
    have h₃₂ : Real.log 2 / Real.log 3 > 0 := by
      apply div_pos
      · exact Real.log_pos (by norm_num)
      · exact Real.log_pos (by norm_num)
    have h₃₃ : Real.log 3 / Real.log 2 > 0 := h₃₁
    have h₃₄ : Real.log 2 / Real.log 3 > 0 := h₃₂
    have h₃₅ : (Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3) = 1 := by
      have h₃₅₁ : (Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3) = 1 := by
        field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
          Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
        <;> ring_nf
        <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
          Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)]
        <;> ring_nf
      exact h₃₅₁
    have h₃₆ : Real.sqrt ((Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
      have h₃₆₁ : (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
        have h₃₆₁₁ : 0 < Real.sqrt (Real.log 3 / Real.log 2) := Real.sqrt_pos.mpr h₃₁
        have h₃₆₁₂ : 0 < Real.sqrt (Real.log 2 / Real.log 3) := Real.sqrt_pos.mpr h₃₂
        have h₃₆₁₃ : 0 < Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) := by positivity
        have h₃₆₁₄ : (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 = Real.log 3 / Real.log 2 := by
          rw [Real.sq_sqrt (le_of_lt h₃₁)]
        have h₃₆₁₅ : (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = Real.log 2 / Real.log 3 := by
          rw [Real.sq_sqrt (le_of_lt h₃₂)]
        calc
          (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 = (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 := by rfl
          _ = (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 + (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 + 2 := by
            rw [h₃₆₁₄, h₃₆₁₅]
          _ = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
            have h₃₆₁₆ : 0 < Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) := by positivity
            nlinarith [Real.sq_sqrt (le_of_lt h₃₁), Real.sq_sqrt (le_of_lt h₃₂), h₃₅]
      have h₃₆₂ : Real.sqrt ((Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2) = Real.sqrt ((Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2) := by rw [h₃₆₁]
      rw [h₃₆₂]
      have h₃₆₃ : Real.sqrt ((Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
        rw [Real.sqrt_sq (by positivity)]
      rw [h₃₆₃]
    exact h₃₆
    <;>
    simp_all
    <;>
    linarith
  
  have h₄ : Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
    rw [h₂]
    rw [h₃]
    <;>
    simp_all [Real.sqrt_eq_iff_sq_eq]
    <;>
    ring_nf at *
    <;>
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)] at *
    <;>
    ring_nf at *
    <;>
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  
  rw [h₄]
  <;>
  simp_all [Real.sqrt_eq_iff_sq_eq]
  <;>
  ring_nf at *
  <;>
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)] at *
  <;>
  ring_nf at *
  <;>
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 3)]