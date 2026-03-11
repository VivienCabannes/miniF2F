import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by
  have h_y : x ^ 2 - 10 * x = 39 := by
    have h₅ : (x ^ 2 - 10 * x - 45) ≠ 0 := by simpa using h₂
    have h₆ : (x ^ 2 - 10 * x - 29) ≠ 0 := by simpa using h₁
    have h₇ : (x ^ 2 - 10 * x - 69) ≠ 0 := by simpa using h₃
    have h₈ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0 := h₄
    have h₉ : (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) + (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 69) - 2 * (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) = 0 := by
      have h₉₁ : (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) + (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 69) - 2 * (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) = 0 := by
        field_simp [h₅, h₆, h₇, sub_eq_zero, add_eq_zero_iff_eq_neg] at h₈
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h₆), sq_pos_of_ne_zero (sub_ne_zero.mpr h₅), sq_pos_of_ne_zero (sub_ne_zero.mpr h₇)]
      exact h₉₁
    have h₁₀ : x ^ 2 - 10 * x = 39 := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h₆), sq_pos_of_ne_zero (sub_ne_zero.mpr h₅), sq_pos_of_ne_zero (sub_ne_zero.mpr h₇)]
    exact h₁₀
  
  have h_final : x = 13 := by
    have h₅ : x = 13 := by
      have h₅₁ : x = 13 ∨ x = -3 := by
        have h₅₂ : x ^ 2 - 10 * x - 39 = 0 := by
          nlinarith
        have h₅₃ : (x - 13) * (x + 3) = 0 := by
          nlinarith
        have h₅₄ : x - 13 = 0 ∨ x + 3 = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero h₅₃
        cases h₅₄ with
        | inl h₅₄ =>
          have h₅₅ : x = 13 := by linarith
          exact Or.inl h₅₅
        | inr h₅₄ =>
          have h₅₅ : x = -3 := by linarith
          exact Or.inr h₅₅
      cases h₅₁ with
      | inl h₅₁ =>
        exact h₅₁
      | inr h₅₁ =>
        have h₅₂ : x > 0 := h₀
        have h₅₃ : x = -3 := h₅₁
        linarith
    exact h₅
  
  exact h_final