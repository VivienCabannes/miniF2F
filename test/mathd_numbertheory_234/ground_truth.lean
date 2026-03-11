import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_234
  (a b : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
  (h₁ : (10 * a + b)^3 = 912673) :
  a + b = 16 := by
  have h₂ : 10 * a + b ≤ 97 := by
    by_contra h
    have h₂₁ : 10 * a + b ≥ 98 := by
      omega
    have h₂₂ : (10 * a + b) ^ 3 ≥ 98 ^ 3 := by
      exact Nat.pow_le_pow_of_le_left (by omega) 3
    have h₂₃ : 98 ^ 3 > 912673 := by
      norm_num
    have h₂₄ : (10 * a + b) ^ 3 > 912673 := by
      linarith
    linarith
  
  have h₃ : 10 * a + b ≥ 97 := by
    by_contra h
    have h₃₁ : 10 * a + b ≤ 96 := by omega
    have h₃₂ : (10 * a + b) ^ 3 ≤ 96 ^ 3 := by
      exact Nat.pow_le_pow_of_le_left (by omega) 3
    have h₃₃ : 96 ^ 3 < 912673 := by
      norm_num
    have h₃₄ : (10 * a + b) ^ 3 < 912673 := by
      linarith
    linarith
  
  have h₄ : 10 * a + b = 97 := by
    have h₅ : 10 * a + b ≤ 97 := h₂
    have h₆ : 10 * a + b ≥ 97 := h₃
    omega
  
  have h₅ : a = 9 := by
    have h₅₁ : 10 * a + b = 97 := h₄
    have h₅₂ : a ≤ 9 := h₀.2.1
    have h₅₃ : b ≤ 9 := h₀.2.2
    have h₅₄ : 1 ≤ a := h₀.1
    have h₅₅ : a ≥ 9 := by
      by_contra h
      have h₅₅₁ : a ≤ 8 := by omega
      have h₅₅₂ : b = 97 - 10 * a := by
        have h₅₅₃ : 10 * a + b = 97 := h₄
        omega
      have h₅₅₃ : a ≤ 8 := by omega
      interval_cases a <;> norm_num at h₅₁ ⊢ <;> (try omega) <;> (try omega)
    omega
  
  have h₆ : b = 7 := by
    have h₆₁ : 10 * a + b = 97 := h₄
    have h₆₂ : a = 9 := h₅
    rw [h₆₂] at h₆₁
    omega
  
  have h₇ : a + b = 16 := by
    have h₇₁ : a = 9 := h₅
    have h₇₂ : b = 7 := h₆
    rw [h₇₁, h₇₂]
    <;> norm_num
  
  exact h₇