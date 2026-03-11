import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_101 (x : ℝ) (h₀ : x ^ 2 - 5 * x - 4 ≤ 10) : x ≥ -2 ∧ x ≤ 7 := by
  have h₁ : x ^ 2 - 5 * x - 14 ≤ 0 := by
    -- Use `nlinarith` to solve the inequality by linear arithmetic on the real numbers.
    nlinarith [sq_nonneg (x - 5 / 2)]
    <;> nlinarith
    <;> nlinarith
    <;> nlinarith
  
  have h₂ : x ^ 2 - 5 * x - 14 = 0 → x = 7 ∨ x = -2 := by
    intro h
    -- We need to show that the only solutions to the inequality are x = 7 or x = -2.
    -- We start by verifying that these values satisfy the equality.
    apply or_iff_not_imp_right.mpr
    intro h₂
    -- Using the fact that x = 7 or x = -2, we can solve the inequality.
    apply eq_of_sub_eq_zero
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₂)
    -- Simplify the equation to find the exact values of x.
    nlinarith
  
  have h₃ : x < -2 ∨ -2 ≤ x ∧ x ≤ 7 ∨ x > 7 := by
    by_cases h₃ : x < -2 <;>
      by_cases h₄ : x > 7 <;>
        by_cases h₅ : x = -2 <;>
          by_cases h₆ : x = 7 <;>
            simp_all [h₂, le_of_lt, le_of_lt, le_of_lt, le_of_lt, le_of_lt, le_of_lt] <;>
            nlinarith
    <;>
      nlinarith
  
  have h₄ : x < -2 → x ^ 2 - 5 * x - 14 > 0 := by
    intro h
    have h₄ := h₂
    have h₅ := h₃
    cases' h₅ with h₅ h₅
    -- Case 1: x < -2
    -- We need to show that x^2 - 5x - 14 > 0 in this case.
    . nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 7)]
    -- Case 2: -2 ≤ x ≤ 7 or x > 7
    . cases' h₅ with h₅ h₅
      -- Subcase 2.1: -2 ≤ x ≤ 7
      . nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 7)]
      -- Subcase 2.2: x > 7
      . nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 7)]
  
  have h₅ : -2 ≤ x ∧ x ≤ 7 → x ^ 2 - 5 * x - 14 ≤ 0 := by
    rintro ⟨h₅, h₆⟩
    -- We need to show that x^2 - 5x - 14 ≤ 0 given that -2 ≤ x ≤ 7.
    -- This can be verified by checking the quadratic expression at the endpoints and ensuring it does not exceed zero within the interval.
    nlinarith [h₁, h₅, h₆]
  
  have h₆ : x > 7 → x ^ 2 - 5 * x - 14 > 0 := by
    intro hx
    -- We know that if x > 7, then x^2 - 5x - 14 > 0 from the given conditions.
    have h₆ : x > 7 → x ^ 2 - 5 * x - 14 > 0 := by
      intro hx
      have h₇ : x > 7 := hx
      have h₈ : x ^ 2 - 5 * x - 14 > 0 := by
        nlinarith
      exact h₈
    exact h₆ hx
  
  have h₇ : x ≥ -2 ∧ x ≤ 7 := by
    refine' ⟨_, _⟩
    -- We need to prove that x ≥ -2 and x ≤ 7. We will use the given inequalities and logical reasoning to establish this.
    all_goals
      -- For both goals (x ≥ -2 and x ≤ 7), we will use the given inequalities and logical reasoning.
      rcases h₃ with (h₃ | h₃ | h₃) <;>
      -- Consider the three cases provided in h₃: x < -2, -2 ≤ x ≤ 7, and x > 7.
      simp_all [h₂, h₄, h₅, h₆, sq] <;>
      -- Simplify the expressions using the given inequalities and logical reasoning.
      nlinarith
  
  exact h₇