import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_246
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^4 - b * x^2 + x + 5)
  (h₂ : f (-3) = 2) :
  f 3 = 8 := by
  have h₃ : 81 * a - 9 * b = 0 := by
    have h₃₁ : f (-3) = a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 + (-3 : ℝ) + 5 := by
      rw [h₀]
      <;> ring_nf
    rw [h₃₁] at h₂
    ring_nf at h₂ ⊢
    linarith
  
  have h₄ : b = 9 * a := by
    have h₄₁ : 81 * a - 9 * b = 0 := h₃
    have h₄₂ : 9 * a - b = 0 := by linarith
    have h₄₃ : b = 9 * a := by linarith
    exact h₄₃
  
  have h₅ : f 3 = 8 := by
    have h₅₁ : f 3 = a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + (3 : ℝ) + 5 := by
      rw [h₀]
      <;> ring_nf
    rw [h₅₁]
    rw [h₄]
    <;> ring_nf at *
    <;> nlinarith
  
  exact h₅