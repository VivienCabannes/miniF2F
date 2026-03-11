import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1)
  (h₄ : a ≠ c) :
  Real.sqrt ((a - c)^2 + (b - d)^2)= Real.sqrt 10 := by
  have h₅ : a ^ 2 + a - 1 = 0 := by
    have h₅₁ : a ^ 2 + a - 1 = 0 := by
      have h₅₂ : b = a ^ 2 := h₀
      have h₅₃ : a + b = 1 := h₁
      have h₅₄ : a + (a ^ 2) = 1 := by
        rw [h₅₂] at h₅₃
        exact h₅₃
      have h₅₅ : a ^ 2 + a - 1 = 0 := by
        linarith
      exact h₅₅
    exact h₅₁
  
  have h₆ : c ^ 2 + c - 1 = 0 := by
    have h₆₁ : c ^ 2 + c - 1 = 0 := by
      have h₆₂ : d = c ^ 2 := h₂
      have h₆₃ : c + d = 1 := h₃
      have h₆₄ : c + (c ^ 2) = 1 := by
        rw [h₆₂] at h₆₃
        exact h₆₃
      have h₆₅ : c ^ 2 + c - 1 = 0 := by
        linarith
      exact h₆₅
    exact h₆₁
  
  have h₇ : a + c = -1 := by
    have h₇₁ : a + c = -1 := by
      have h₇₂ : a ≠ c := h₄
      have h₇₃ : a ^ 2 + a - 1 = 0 := h₅
      have h₇₄ : c ^ 2 + c - 1 = 0 := h₆
      have h₇₅ : (a - c) * (a + c + 1) = 0 := by
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne h₄), sq_nonneg (a - c), sq_nonneg (a + c)]
      have h₇₆ : a + c + 1 = 0 := by
        apply mul_left_cancel₀ (sub_ne_zero_of_ne h₄)
        nlinarith
      linarith
    exact h₇₁
  
  have h₈ : a * c = -1 := by
    have h₈₁ : a + c = -1 := h₇
    have h₈₂ : a ^ 2 + a - 1 = 0 := h₅
    have h₈₃ : c ^ 2 + c - 1 = 0 := h₆
    have h₈₄ : a * c = -1 := by
      have h₈₅ : (a + c) ^ 2 = a ^ 2 + 2 * a * c + c ^ 2 := by ring
      rw [h₈₁] at h₈₅
      have h₈₆ : a ^ 2 = -a + 1 := by linarith
      have h₈₇ : c ^ 2 = -c + 1 := by linarith
      nlinarith
    exact h₈₄
  
  have h₉ : (a - c) ^ 2 = 5 := by
    have h₉₁ : (a - c) ^ 2 = 5 := by
      have h₉₂ : a ^ 2 + a - 1 = 0 := h₅
      have h₉₃ : c ^ 2 + c - 1 = 0 := h₆
      have h₉₄ : a + c = -1 := h₇
      have h₉₅ : a * c = -1 := h₈
      have h₉₆ : (a - c) ^ 2 = 5 := by
        have h₉₇ : (a - c) ^ 2 = a ^ 2 - 2 * a * c + c ^ 2 := by ring
        rw [h₉₇]
        have h₉₈ : a ^ 2 = -a + 1 := by linarith
        have h₉₉ : c ^ 2 = -c + 1 := by linarith
        rw [h₉₈, h₉₉]
        nlinarith
      exact h₉₆
    exact h₉₁
  
  have h₁₀ : (b - d) ^ 2 = 5 := by
    have h₁₀₁ : b - d = -(a - c) := by
      have h₁₀₂ : b = a ^ 2 := h₀
      have h₁₀₃ : d = c ^ 2 := h₂
      have h₁₀₄ : a + c = -1 := h₇
      have h₁₀₅ : a * c = -1 := h₈
      have h₁₀₆ : b - d = a ^ 2 - c ^ 2 := by
        rw [h₁₀₂, h₁₀₃]
        <;> ring
      have h₁₀₇ : a ^ 2 - c ^ 2 = (a - c) * (a + c) := by
        ring
      have h₁₀₈ : b - d = (a - c) * (a + c) := by
        rw [h₁₀₆, h₁₀₇]
      have h₁₀₉ : b - d = -(a - c) := by
        rw [h₁₀₈, h₁₀₄]
        <;> ring
        <;> linarith
      exact h₁₀₉
    have h₁₀₂ : (b - d) ^ 2 = 5 := by
      rw [h₁₀₁]
      have h₁₀₃ : (a - c) ^ 2 = 5 := h₉
      have h₁₀₄ : (-(a - c)) ^ 2 = (a - c) ^ 2 := by
        ring
      rw [h₁₀₄]
      linarith
    exact h₁₀₂
  
  have h₁₁ : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    have h₁₁₁ : (a - c) ^ 2 = 5 := h₉
    have h₁₁₂ : (b - d) ^ 2 = 5 := h₁₀
    linarith
  
  have h₁₂ : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
    rw [h₁₁]
    <;>
    simp [Real.sqrt_eq_iff_sq_eq]
    <;>
    ring_nf at *
    <;>
    nlinarith
  
  rw [h₁₂]