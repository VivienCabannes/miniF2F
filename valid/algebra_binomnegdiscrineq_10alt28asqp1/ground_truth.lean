import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_binomnegdiscrineq_10alt28asqp1 (a : ℝ) : 10 * a ≤ 28 * a ^ 2 + 1 := by
  have h1 : 28 * a ^ 2 - 10 * a + 1 ≥ 0 := by
    -- We use the fact that the square of any real number is non-negative.
    have h₀ : 0 ≤ (a - 5 / 28) ^ 2 := sq_nonneg _
    -- We also know that 28 is a positive number.
    have h₁ : 0 < 28 := by norm_num
    -- Using the non-negativity of the square and the positivity of 28, we can conclude the inequality.
    nlinarith [h₀, h₁]
  
  have h2 : ∀ (a : ℝ), 28 * a ^ 2 - 10 * a + 1 ≥ 0 := by
    intro a
    have h2 : 28 * a ^ 2 - 10 * a + 1 ≥ 0 := by
      -- Use the given inequality as a starting point
      have h2 := h1
      -- Use non-linear arithmetic to verify the inequality
      nlinarith [sq_nonneg (a - 5 / 28)]
    -- Use linear arithmetic to conclude the proof
    linarith
  
  have h3 : ∀ (a : ℝ), 28 * a ^ 2 - 10 * a + 1 ≥ 0 → 10 * a ≤ 28 * a ^ 2 + 1 := by
    intro a h
    have h' := h2 a
    linarith
  
  -- Use the fact that the discriminant of the quadratic equation is negative to show that the function is always non-negative.
  have h4 := h3 a h1
  -- Use linear arithmetic to conclude the proof.
  linarith