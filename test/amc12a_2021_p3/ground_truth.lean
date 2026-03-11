import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2021_p3
  (x y : ℕ)
  (h₀ : x + y = 17402)
  (h₁ : 10∣x)
  (h₂ : x / 10 = y) :
  ↑x - ↑y = (14238:ℤ) := by
  have h₃ : x = 10 * y := by
    have h₃₁ : x = 10 * (x / 10) := by
      have h₃₁₁ : 10 ∣ x := h₁
      have h₃₁₂ : x = 10 * (x / 10) := by
        have h₃₁₃ : x = 10 * (x / 10) := by
          have h₃₁₄ : x / 10 * 10 = x := by
            apply Nat.div_mul_cancel h₁
          omega
        exact h₃₁₃
      exact h₃₁₂
    rw [h₂] at h₃₁
    <;> linarith
  
  have h₄ : y = 1582 := by
    have h₄₁ : 11 * y = 17402 := by
      have h₄₂ : x = 10 * y := h₃
      rw [h₄₂] at h₀
      ring_nf at h₀ ⊢
      <;> omega
    have h₄₂ : y = 1582 := by
      omega
    exact h₄₂
  
  have h₅ : x = 15820 := by
    rw [h₃, h₄]
    <;> norm_num
  
  have h₆ : (x : ℤ) - (y : ℤ) = (14238 : ℤ) := by
    rw [h₅, h₄]
    <;> norm_num
    <;> rfl
  
  exact h₆