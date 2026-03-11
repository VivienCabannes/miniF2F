import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_36azm9asqle36zsq (z a : ℝ) : 36 * (a * z) - 9 * a ^ 2 ≤ 36 * z ^ 2 := by
  have step1 : 4 * (a * z) - a ^ 2 ≤ 4 * z ^ 2 := by
    -- Normalize the expression by expanding and simplifying it.
    ring_nf
    -- Recognize that the inequality can be rewritten as a square of a binomial.
    have h₁ : 0 ≤ (a - 2 * z) ^ 2 := sq_nonneg _
    -- Use the non-negativity of the square to conclude the proof.
    linarith
  
  have step2 : 4 * z ^ 2 - 4 * a * z + a ^ 2 ≥ 0 := by
    -- Recognize that the expression can be rewritten as a square of a binomial.
    have h1 : 0 ≤ (2 * z - a) ^ 2 := by apply sq_nonneg
    -- Simplify the inequality using the non-negativity of the square term.
    linarith [h1]
  
  have step3 : 4 * z ^ 2 - 4 * a * z + a ^ 2 = (2 * z - a) ^ 2 := by
    -- Simplify the expression using algebraic identities and properties.
    simp [sq, mul_add, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_left_comm]
    -- Use the ring tactic to simplify the expression and verify the identity.
    <;> ring
  
  have step4 : (2 * z - a) ^ 2 ≥ 0 := by
    -- Use the given equation step3 to rewrite the expression
    have h : (2 * z - a) ^ 2 ≥ 0 := by
      -- Use the fact that the square of any real number is non-negative
      nlinarith [sq_nonneg (2 * z - a)]
    -- Conclude the proof using the previously derived inequality
    linarith
  
  have step5 : 36 * (a * z) - 9 * a ^ 2 ≤ 36 * z ^ 2 := by
    -- We start by using the given inequalities to derive the desired result.
    have h1 : 36 * (a * z) - 9 * a ^ 2 ≤ 36 * z ^ 2 := by
      -- We use the given inequality step1 to help us derive the result.
      linarith [step1, step2, step3, step4]
    -- Finally, we use the derived inequality to conclude the proof.
    linarith [h1]
  
  linarith [step2, step4, step5]
  -- Use linear arithmetic to verify the inequality based on the given steps.
  -- This includes checking that the expression remains non-negative and that the inequality holds after transformations.
  <;> nlinarith
  -- Use nonlinear arithmetic to handle more complex expressions and ensure the inequality holds.
  <;> nlinarith
  -- Use nonlinear arithmetic again to ensure all steps are verified and the inequality is correct.
  <;> nlinarith