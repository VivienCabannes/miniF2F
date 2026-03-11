import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_452
  (a : ℕ → ℝ)
  (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
  (h₁ : a 1 = 2 / 3)
  (h₂ : a 9 = 4 / 5) :
  a 5 = 11 / 15 := by
  have h₃ : a 2 - a 1 = a 1 - a 0 := by
    have h₃₁ := h₀ 0
    norm_num at h₃₁ ⊢
    <;> linarith
  
  have h₄ : a 3 - a 2 = a 1 - a 0 := by
    have h₄₁ := h₀ 1
    have h₄₂ := h₀ 0
    have h₄₃ : a 3 - a 2 = a 2 - a 1 := by
      linarith
    linarith
  
  have h₅ : a 4 - a 3 = a 1 - a 0 := by
    have h₅₁ := h₀ 2
    have h₅₂ := h₀ 1
    have h₅₃ := h₀ 0
    have h₅₄ : a 4 - a 3 = a 3 - a 2 := by linarith
    linarith
  
  have h₆ : a 5 - a 4 = a 1 - a 0 := by
    have h₆₁ := h₀ 3
    have h₆₂ := h₀ 2
    have h₆₃ := h₀ 1
    have h₆₄ := h₀ 0
    have h₆₅ : a 5 - a 4 = a 4 - a 3 := by linarith
    linarith
  
  have h₇ : a 6 - a 5 = a 1 - a 0 := by
    have h₇₁ := h₀ 4
    have h₇₂ := h₀ 3
    have h₇₃ := h₀ 2
    have h₇₄ := h₀ 1
    have h₇₅ := h₀ 0
    have h₇₆ : a 6 - a 5 = a 5 - a 4 := by linarith
    linarith
  
  have h₈ : a 7 - a 6 = a 1 - a 0 := by
    have h₈₁ := h₀ 5
    have h₈₂ := h₀ 4
    have h₈₃ := h₀ 3
    have h₈₄ := h₀ 2
    have h₈₅ := h₀ 1
    have h₈₆ := h₀ 0
    have h₈₇ : a 7 - a 6 = a 6 - a 5 := by linarith
    linarith
  
  have h₉ : a 8 - a 7 = a 1 - a 0 := by
    have h₉₁ := h₀ 6
    have h₉₂ := h₀ 5
    have h₉₃ := h₀ 4
    have h₉₄ := h₀ 3
    have h₉₅ := h₀ 2
    have h₉₆ := h₀ 1
    have h₉₇ := h₀ 0
    have h₉₈ : a 8 - a 7 = a 7 - a 6 := by linarith
    linarith
  
  have h₁₀ : a 9 - a 8 = a 1 - a 0 := by
    have h₁₀₁ := h₀ 7
    have h₁₀₂ := h₀ 6
    have h₁₀₃ := h₀ 5
    have h₁₀₄ := h₀ 4
    have h₁₀₅ := h₀ 3
    have h₁₀₆ := h₀ 2
    have h₁₀₇ := h₀ 1
    have h₁₀₈ := h₀ 0
    have h₁₀₉ : a 9 - a 8 = a 8 - a 7 := by linarith
    linarith
  
  have h₁₁ : a 9 - a 1 = 8 * (a 1 - a 0) := by
    have h₁₁₁ : a 9 - a 1 = (a 9 - a 8) + (a 8 - a 7) + (a 7 - a 6) + (a 6 - a 5) + (a 5 - a 4) + (a 4 - a 3) + (a 3 - a 2) + (a 2 - a 1) := by
      linarith
    rw [h₁₁₁]
    have h₁₁₂ : a 9 - a 8 = a 1 - a 0 := by linarith
    have h₁₁₃ : a 8 - a 7 = a 1 - a 0 := by linarith
    have h₁₁₄ : a 7 - a 6 = a 1 - a 0 := by linarith
    have h₁₁₅ : a 6 - a 5 = a 1 - a 0 := by linarith
    have h₁₁₆ : a 5 - a 4 = a 1 - a 0 := by linarith
    have h₁₁₇ : a 4 - a 3 = a 1 - a 0 := by linarith
    have h₁₁₈ : a 3 - a 2 = a 1 - a 0 := by linarith
    have h₁₁₉ : a 2 - a 1 = a 1 - a 0 := by linarith
    linarith
  
  have h₁₂ : a 1 - a 0 = 1 / 60 := by
    have h₁₂₁ : a 9 - a 1 = 8 * (a 1 - a 0) := h₁₁
    have h₁₂₂ : a 9 - a 1 = 2 / 15 := by
      rw [h₂, h₁]
      <;> norm_num
    have h₁₂₃ : 8 * (a 1 - a 0) = 2 / 15 := by linarith
    have h₁₂₄ : a 1 - a 0 = 1 / 60 := by
      ring_nf at h₁₂₃ ⊢
      linarith
    exact h₁₂₄
  
  have h₁₃ : a 5 - a 1 = 4 * (a 1 - a 0) := by
    have h₁₃₁ : a 5 - a 1 = (a 5 - a 4) + (a 4 - a 3) + (a 3 - a 2) + (a 2 - a 1) := by
      ring
    rw [h₁₃₁]
    have h₁₃₂ : a 5 - a 4 = a 1 - a 0 := h₆
    have h₁₃₃ : a 4 - a 3 = a 1 - a 0 := h₅
    have h₁₃₄ : a 3 - a 2 = a 1 - a 0 := h₄
    have h₁₃₅ : a 2 - a 1 = a 1 - a 0 := h₃
    linarith
  
  have h₁₄ : a 5 - a 1 = 1 / 15 := by
    rw [h₁₃, h₁₂]
    <;> ring_nf
    <;> norm_num
  
  have h₁₅ : a 5 = 11 / 15 := by
    have h₁₅₁ : a 5 = 11 / 15 := by
      have h₁₅₂ : a 5 - a 1 = 1 / 15 := h₁₄
      have h₁₅₃ : a 1 = 2 / 3 := h₁
      have h₁₅₄ : a 5 = 11 / 15 := by
        linarith
      exact h₁₅₄
    exact h₁₅₁
  
  apply h₁₅