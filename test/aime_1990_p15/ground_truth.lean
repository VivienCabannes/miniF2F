import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x^2 + b * y^2 = 7)
  (h₂ : a * x^3 + b * y^3 = 16)
  (h₃ : a * x^4 + b * y^4 = 42) :
  a * x^5 + b * y^5 = 20 := by
  have h_sum_xy : x + y = -14 := by
    have h₄ : 7 * (x + y) - 3 * (x * y) = 16 := by
      have h₄₁ : a * x ^ 3 + b * y ^ 3 = (x + y) * (a * x ^ 2 + b * y ^ 2) - x * y * (a * x + b * y) := by
        ring
      rw [h₂, h₁, h₀] at h₄₁
      linarith
    have h₅ : 16 * (x + y) - 7 * (x * y) = 42 := by
      have h₅₁ : a * x ^ 4 + b * y ^ 4 = (x + y) * (a * x ^ 3 + b * y ^ 3) - x * y * (a * x ^ 2 + b * y ^ 2) := by
        ring
      rw [h₃, h₂, h₁] at h₅₁
      linarith
    have h₆ : x + y = -14 := by
      linarith
    exact h₆
  
  have h_prod_xy : x * y = -38 := by
    have h₄ : 7 * (x + y) - 3 * (x * y) = 16 := by
      have h₄₁ : a * x ^ 3 + b * y ^ 3 = (x + y) * (a * x ^ 2 + b * y ^ 2) - x * y * (a * x + b * y) := by
        ring
      rw [h₂, h₁, h₀] at h₄₁
      linarith
    have h₅ : 16 * (x + y) - 7 * (x * y) = 42 := by
      have h₅₁ : a * x ^ 4 + b * y ^ 4 = (x + y) * (a * x ^ 3 + b * y ^ 3) - x * y * (a * x ^ 2 + b * y ^ 2) := by
        ring
      rw [h₃, h₂, h₁] at h₅₁
      linarith
    have h₆ : x * y = -38 := by
      linarith
    exact h₆
  
  have h_sum_ab : a + b = 49 / 38 := by
    have h₄ : (x + y) * (a * x + b * y) = (a * x ^ 2 + b * y ^ 2) + x * y * (a + b) := by
      ring
    rw [h₀, h₁, h_sum_xy, h_prod_xy] at h₄
    <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (a + b), sq_nonneg (a - b)]
  
  have h_recurrence : a * x ^ 5 + b * y ^ 5 = 20 := by
    have h₅ : a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - x * y * (a * x ^ 3 + b * y ^ 3) := by
      ring
    rw [h₅]
    rw [h₃, h₂, h_sum_xy, h_prod_xy]
    <;> ring_nf
    <;> linarith
  
  exact h_recurrence