import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2002_p6 (a b : ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : ∀ x, x ^ 2 + a * x + b = (x - a) * (x - b)) : a = 1 ∧ b = -2 := by
  have h₂ : a + b = -a := by
    -- Evaluate the polynomial at x = 0 to get an equation involving b.
    have h₂ := h₁ 0
    -- Evaluate the polynomial at x = 1 to get another equation involving a and b.
    have h₃ := h₁ 1
    -- Simplify the equations obtained from the polynomial identity.
    simp_all
    -- Use linear arithmetic to solve for a + b.
    <;> linarith
  
  have h₃ : a * b = b := by
    have h₃ := h₁ 1
    have h₄ := h₁ (-1)
    have h₅ := h₁ 0
    simp_all
    <;> nlinarith
  
  have h₄ : b = -2 * a := by
    have h₄ := h₁ 1
    have h₅ := h₁ 0
    have h₆ := h₁ a
    have h₇ := h₁ b
    simp_all [mul_comm, mul_assoc, mul_left_comm]
    <;> linarith
  
  have h₅ : b * (a - 1) = 0 := by
    -- Substitute b = -2a into the polynomial equation and simplify
    rw [h₄] at h₁
    -- Evaluate the polynomial at x = 0, 1, and -1
    have h₅ := h₁ 0
    have h₆ := h₁ 1
    have h₇ := h₁ (-1)
    -- Simplify the equations obtained from the evaluations
    simp_all
    -- Use linear arithmetic to conclude that b*(a - 1) = 0
    <;> nlinarith
  
  have h₆ : a = 1 := by
    -- We need to show that a = 1. We will do this by assuming a ≠ 1 and deriving a contradiction.
    have : a = 1 := by
      apply mul_left_cancel₀ (sub_ne_zero_of_ne h₀.2)
      -- We use the fact that b ≠ 0 to cancel b from both sides of the equation.
      rw [← sub_eq_zero] at h₅ ⊢
      -- We rewrite the equation to prepare for simplification.
      nlinarith [h₁ 0, h₁ 1, h₁ a, h₁ b, h₂, h₃, h₄, h₅]
    -- We have shown that a = 1, so we conclude with this fact.
    simpa [h₀.1, h₀.2] using this
  
  have h₇ : b = -2 := by
    have h₇ := h₁ 0
    have h₈ := h₁ 1
    have h₉ := h₁ (-2)
    have h₁₀ := h₁ 1
    simp_all
  
  -- We start by constructing the conjunction (a = 1 ∧ b = -2) and then prove each part separately.
  constructor
  -- First, we prove that a = 1.
  all_goals
    -- All goals are to prove that a = 1 and b = -2.
    -- We use the given conditions and logical deductions to prove this.
    nlinarith [h₁ 0, h₁ 1, h₁ (-2), h₁ 3, h₁ (-3), h₁ 2, h₁ (-1), h₁ 1, h₁ (-2), h₁ 3, h₁ (-3), h₁ 2, h₁ (-1)]