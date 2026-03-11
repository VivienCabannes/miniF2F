import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2020_p10
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) :
  (Nat.digits 10 n).sum = 13 := by
  have h₀' : 1 < n := by
    by_contra h
    push_neg at h
    interval_cases n
    simp [Real.logb] at h₁
  have h2 : (n : ℝ) > 1 := by exact_mod_cast h₀'
  have h3 : Real.logb 16 n = Real.logb 2 n / 4 := by
    have h4 : Real.logb 16 n = Real.logb 2 n / Real.logb 2 (16 : ℝ) := by
      field_simp [Real.logb]
    have h5 : Real.logb 2 (16 : ℝ) = 4 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h4, h5]
  have h6 : Real.logb 4 n = Real.logb 2 n / 2 := by
    have h7 : Real.logb 4 n = Real.logb 2 n / Real.logb 2 (4 : ℝ) := by
      field_simp [Real.logb]
    have h8 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h7, h8]
  rw [h3] at h₁
  rw [h6] at h₁
  have h9 : Real.logb 2 (Real.logb 2 n / 4) = Real.logb 2 (Real.logb 2 n) - 2 := by
    have h10 : Real.logb 2 n > 0 := by
      apply Real.logb_pos <;> linarith
    rw [Real.logb_div (by linarith) (by norm_num)]
    have h13 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    linarith
  have h10 : Real.logb 4 (Real.logb 2 n / 2) = (Real.logb 2 (Real.logb 2 n / 2) ) / 2 := by
    have h14 : Real.logb 4 (Real.logb 2 n / 2) = Real.logb 2 (Real.logb 2 n / 2) / Real.logb 2 (4 : ℝ) := by
      field_simp [Real.logb]
    have h15 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h14, h15]
  have h11 : Real.logb 2 (Real.logb 2 n / 2) = Real.logb 2 (Real.logb 2 n) - 1 := by
    have h12 : Real.logb 2 n > 0 := by
      apply Real.logb_pos <;> linarith
    rw [Real.logb_div (by linarith) (by norm_num)]
    have h15 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    linarith
  rw [h9, h10, h11] at h₁
  have h13 : Real.logb 2 (Real.logb 2 n) = 3 := by nlinarith
  have h14 : Real.logb 2 n = 8 := by
    have h16 : Real.logb 2 n = (2 : ℝ) ^ (3 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] at h13
      · linarith
      all_goals
      have h17 : Real.logb 2 n > 0 := by
        apply Real.logb_pos <;> linarith
      all_goals try linarith
      all_goals try positivity
    norm_num at h16 ⊢
    linarith
  have h18 : (n : ℝ) = 256 := by
    have h20 : (n : ℝ) = (2 : ℝ) ^ (8 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] at h14
      · linarith
      all_goals try linarith
      all_goals try positivity
    norm_num at h20 ⊢
    linarith
  have h19 : n = 256 := by exact_mod_cast h18
  rw [h19]
  norm_num
