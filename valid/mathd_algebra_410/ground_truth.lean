import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_410 (x y : ℝ) (h₀ : y = x ^ 2 - 6 * x + 13) : 4 ≤ y := by
  have h₁ : y = (x - 3)^2 + 4 := by
    -- Start with the given equation for y
    rw [h₀]
    -- Simplify the expression by completing the square
    have h₁ : x ^ 2 - 6 * x + 13 = (x - 3) ^ 2 + 4 := by
      ring
    -- Substitute the simplified expression back into the equation for y
    rw [h₁]
  
  have h₂ : ∀ (x : ℝ), (x - 3)^2 + 4 ≥ 4 := by
    intro x
    -- Use the fact that the square of any real number is non-negative
    nlinarith [sq_nonneg (x - 3)]
  
  have h₃ : 4 ≤ y := by
    -- We need to show that 4 ≤ y. We can use the fact that y = (x - 3)^2 + 4, which is always ≥ 4.
    have h₃ := h₂ 0
    have h₄ := h₂ 1
    have h₅ := h₂ (-1)
    have h₆ := h₂ 2
    have h₇ := h₂ (-2)
    -- Simplify the expressions for y using the given forms.
    simp_all only [sq, mul_one, mul_neg, mul_zero, sub_zero, sub_neg_eq_add, add_zero,
      add_right_neg, add_zero]
    -- Use linear arithmetic to conclude that 4 ≤ y.
    <;> nlinarith
  
  -- Since we have the equality y = (x - 3)^2 + 4, we can use the fact that (x - 3)^2 is always non-negative.
  -- This means that y is always at least 4, as shown by the equality.
  linarith [h₂ x, h₂ 3, h₂ 0, h₂ 1, h₂ 2, h₂ 4, h₂ 5, h₂ 6]