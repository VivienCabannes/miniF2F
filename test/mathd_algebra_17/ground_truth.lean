import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_17
  (a : ℝ)
  (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
  a = 8 := by
  have h₁ : 16 + 16 * a ≥ 0 := by
    by_contra h
    have h₂ : 16 + 16 * a < 0 := by linarith
    have h₃ : Real.sqrt (16 + 16 * a) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
    have h₄ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 := by
      rw [h₃]
      have h₅ : Real.sqrt (4 + (0 : ℝ)) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      exact h₅
    have h₅ : Real.sqrt (1 + Real.sqrt (1 + a)) = 4 := by
      have h₅₁ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := h₀
      rw [h₄] at h₅₁
      have h₅₂ : 2 + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by linarith
      have h₅₃ : Real.sqrt (1 + Real.sqrt (1 + a)) = 4 := by linarith
      exact h₅₃
    have h₆ : 1 + Real.sqrt (1 + a) = 16 := by
      have h₆₁ : Real.sqrt (1 + Real.sqrt (1 + a)) = 4 := h₅
      have h₆₂ : 1 + Real.sqrt (1 + a) ≥ 0 := by
        by_contra h₆₂
        have h₆₃ : 1 + Real.sqrt (1 + a) < 0 := by linarith
        have h₆₄ : Real.sqrt (1 + Real.sqrt (1 + a)) = 0 := by
          rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
        rw [h₆₄] at h₆₁
        norm_num at h₆₁
      have h₆₃ : Real.sqrt (1 + Real.sqrt (1 + a)) = 4 := h₅
      have h₆₄ : Real.sqrt (1 + Real.sqrt (1 + a)) ^ 2 = 4 ^ 2 := by rw [h₆₃]
      have h₆₅ : 1 + Real.sqrt (1 + a) = 16 := by
        nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt (1 + a))]
      exact h₆₅
    have h₇ : Real.sqrt (1 + a) = 15 := by linarith
    have h₈ : 1 + a ≥ 0 := by
      by_contra h₈
      have h₉ : 1 + a < 0 := by linarith
      have h₁₀ : Real.sqrt (1 + a) = 0 := by
        rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
      rw [h₁₀] at h₇
      norm_num at h₇
    have h₉ : Real.sqrt (1 + a) = 15 := h₇
    have h₁₀ : 1 + a = 225 := by
      have h₁₀₁ : Real.sqrt (1 + a) = 15 := h₉
      have h₁₀₂ : Real.sqrt (1 + a) ^ 2 = 15 ^ 2 := by rw [h₁₀₁]
      have h₁₀₃ : 1 + a = 225 := by
        nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + a)]
      exact h₁₀₃
    have h₁₁ : a = 224 := by linarith
    have h₁₂ : a < -1 := by
      linarith
    linarith
  
  have h₂ : 1 + a ≥ 0 := by
    by_contra h
    have h₃ : 1 + a < 0 := by linarith
    have h₄ : Real.sqrt (1 + a) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
    have h₅ : Real.sqrt (1 + Real.sqrt (1 + a)) = 1 := by
      rw [h₄]
      have h₅₁ : Real.sqrt (1 + (0 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      exact h₅₁
    have h₆ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 5 := by
      have h₆₁ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := h₀
      rw [h₅] at h₆₁
      have h₆₂ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + 1 = 6 := by linarith
      have h₆₃ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 5 := by linarith
      exact h₆₃
    have h₇ : 4 + Real.sqrt (16 + 16 * a) = 25 := by
      have h₇₁ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 5 := h₆
      have h₇₂ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) ^ 2 = 5 ^ 2 := by rw [h₇₁]
      have h₇₃ : 4 + Real.sqrt (16 + 16 * a) ≥ 0 := by
        by_contra h₇₃
        have h₇₄ : 4 + Real.sqrt (16 + 16 * a) < 0 := by linarith
        have h₇₅ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 0 := by
          rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
        rw [h₇₅] at h₇₁
        norm_num at h₇₅ h₇₁ ⊢
        <;> linarith
      have h₇₄ : 4 + Real.sqrt (16 + 16 * a) = 25 := by
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (4 + Real.sqrt (16 + 16 * a) : ℝ))]
      exact h₇₄
    have h₈ : Real.sqrt (16 + 16 * a) = 21 := by linarith
    have h₉ : 16 + 16 * a = 441 := by
      have h₉₁ : Real.sqrt (16 + 16 * a) = 21 := h₈
      have h₉₂ : Real.sqrt (16 + 16 * a) ^ 2 = 21 ^ 2 := by rw [h₉₁]
      have h₉₃ : 16 + 16 * a ≥ 0 := by linarith
      have h₉₄ : 16 + 16 * a = 441 := by
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (16 + 16 * a : ℝ))]
      exact h₉₄
    have h₁₀ : a < -1 := by linarith
    have h₁₁ : a ≥ -1 := by
      nlinarith
    linarith
  
  have h₃ : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
    have h₃₁ : Real.sqrt (16 + 16 * a) = Real.sqrt (16 * (1 + a)) := by
      ring_nf
      <;> field_simp
      <;> ring_nf
    rw [h₃₁]
    have h₃₂ : Real.sqrt (16 * (1 + a)) = 4 * Real.sqrt (1 + a) := by
      rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)]
      nlinarith [Real.sq_sqrt (show 0 ≤ 1 + a by linarith), Real.sqrt_nonneg (1 + a)]
    rw [h₃₂]
    <;> ring
    <;> field_simp
    <;> ring_nf
    <;> linarith
  
  have h₄ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    rw [h₃]
    have h₄₁ : Real.sqrt (4 + (4 : ℝ) * Real.sqrt (1 + a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
      have h₄₂ : Real.sqrt (4 + (4 : ℝ) * Real.sqrt (1 + a)) = Real.sqrt (4 * (1 + Real.sqrt (1 + a))) := by
        have h₄₃ : (4 : ℝ) + (4 : ℝ) * Real.sqrt (1 + a) = 4 * (1 + Real.sqrt (1 + a)) := by ring
        rw [h₄₃]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
      rw [h₄₂]
      have h₄₄ : Real.sqrt (4 * (1 + Real.sqrt (1 + a))) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
        have h₄₅ : Real.sqrt (4 * (1 + Real.sqrt (1 + a))) = Real.sqrt 4 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
          rw [← Real.sqrt_mul] <;> nlinarith [Real.sqrt_nonneg (1 + a), Real.sqrt_nonneg (1 + Real.sqrt (1 + a)), Real.sq_sqrt (show 0 ≤ 1 + a by linarith), Real.sq_sqrt (show 0 ≤ 1 + Real.sqrt (1 + a) by positivity)]
        rw [h₄₅]
        have h₄₆ : Real.sqrt 4 = 2 := by norm_num [Real.sqrt_eq_iff_sq_eq]
        rw [h₄₆]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
      rw [h₄₄]
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
    rw [h₄₁]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  
  have h₅ : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
    have h₅₁ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := h₀
    rw [h₄] at h₅₁
    have h₅₂ : 2 * Real.sqrt (1 + Real.sqrt (1 + a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by linarith
    have h₅₃ : 3 * Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by linarith
    have h₅₄ : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by linarith
    exact h₅₄
  
  have h₆ : 1 + Real.sqrt (1 + a) = 4 := by
    have h₆₁ : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := h₅
    have h₆₂ : Real.sqrt (1 + Real.sqrt (1 + a)) ^ 2 = 2 ^ 2 := by rw [h₆₁]
    have h₆₃ : 1 + Real.sqrt (1 + a) ≥ 0 := by
      by_contra h₆₃
      have h₆₄ : 1 + Real.sqrt (1 + a) < 0 := by linarith
      have h₆₅ : Real.sqrt (1 + Real.sqrt (1 + a)) = 0 := by
        rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
      rw [h₆₅] at h₆₁
      norm_num at h₆₁
      <;> linarith
    have h₆₄ : 1 + Real.sqrt (1 + a) = 4 := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + Real.sqrt (1 + a) : ℝ))]
    exact h₆₄
  
  have h₇ : Real.sqrt (1 + a) = 3 := by
    have h₇₁ : 1 + Real.sqrt (1 + a) = 4 := h₆
    have h₇₂ : Real.sqrt (1 + a) = 3 := by linarith
    exact h₇₂
  
  have h₈ : 1 + a = 9 := by
    have h₈₁ : Real.sqrt (1 + a) = 3 := h₇
    have h₈₂ : Real.sqrt (1 + a) ^ 2 = 3 ^ 2 := by rw [h₈₁]
    have h₈₃ : 1 + a ≥ 0 := by linarith
    have h₈₄ : 1 + a = 9 := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + a : ℝ))]
    exact h₈₄
  
  have h₉ : a = 8 := by
    linarith
  
  exact h₉