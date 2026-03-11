import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1961_p1 (x y z a b : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x ≠ y) (h₂ : y ≠ z)
  (h₃ : z ≠ x) (h₄ : x + y + z = a) (h₅ : x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2) (h₆ : x * y = z ^ 2) :
  0 < a ∧ b ^ 2 < a ^ 2 ∧ a ^ 2 < 3 * b ^ 2 := by
  have h₇ : z = sqrt (x * y) := by
    have h₇ : 0 < x * y := by nlinarith
    have h₈ : 0 < z := by nlinarith
    have h₉ : z = sqrt (x * y) := by
      apply Eq.symm
      rw [sqrt_eq_iff_mul_self_eq] <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - z), sq_nonneg (x * y - z ^ 2)]
    exact h₉
  
  have h₈ : x + y + sqrt (x * y) = a := by
    -- We already have the equation x + y + z = a from the problem statement.
    have h₄' : x + y + z = a := h₄
    -- Substitute z = sqrt(xy) into the equation x + y + z = a and simplify.
    rw [h₇] at h₄'
    -- Use nlinarith to handle the arithmetic and properties of square roots.
    nlinarith [Real.sqrt_nonneg (x * y), h₀.1, h₀.2.1, h₀.2.2, h₁, h₂, h₃]
  
  have h₉ : x^2 + y^2 + x * y = b^2 := by
    -- Step 2: Analyze the given condition and derive the required equation.
    have h₉ : 0 < x * y := mul_pos h₀.1 h₀.2.1
    -- Step 3: Use the condition z = sqrt(xy) to derive a useful equation.
    have h₁₀ : z = sqrt (x * y) := h₇
    -- Step 4: Substitute z = sqrt(xy) into the sum equation.
    rw [h₁₀] at h₄
    -- Step 5: Substitute z = sqrt(xy) into the sum of squares equation.
    rw [h₁₀] at h₅
    -- Step 6: Simplify the equation using algebraic manipulation.
    nlinarith [sq_sqrt (mul_nonneg h₀.1.le h₀.2.1.le)]
  
  have h₁₀ : a > 0 := by
    -- We start by noting that the product of x and y is positive.
    have h₁₀ : 0 < x * y := by
      nlinarith
    -- Since z is the square root of x * y, z is non-negative.
    have h₁₁ : 0 ≤ z := by
      nlinarith
    -- From the given conditions, we can directly conclude that a is positive.
    nlinarith
  
  have h₁₁ : b^2 < a^2 := by
    have h₁₁ : 0 < x * y := by
      nlinarith [sq_sqrt (mul_nonneg (le_of_lt h₀.1) (le_of_lt h₀.2.1))]
    -- Using the given conditions and the properties of real numbers, we derive that x * y is positive.
    nlinarith [sq_sqrt (mul_nonneg (le_of_lt h₀.1) (le_of_lt h₀.2.1)), h₅, h₄, h₆, h₇, h₈, h₉]
  
  have h₁₂ : a^2 < 3 * b^2 := by
    have h₁₂ := sq_pos_of_ne_zero (sub_ne_zero_of_ne h₁) -- h₁₂: (x - y)^2 > 0
    have h₁₃ := sq_pos_of_ne_zero (sub_ne_zero_of_ne h₂) -- h₁₃: (y - z)^2 > 0
    have h₁₄ := sq_pos_of_ne_zero (sub_ne_zero_of_ne h₃) -- h₁₄: (z - x)^2 > 0
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  -- Using the given conditions and derived equations, we can directly conclude the required inequalities.
  refine' ⟨by nlinarith [h₁₀], by nlinarith [h₁₁], by nlinarith [h₁₂]⟩