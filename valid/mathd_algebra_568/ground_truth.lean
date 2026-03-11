import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_568 (a : ℝ) :
    (a - 1) * (a + 1) * (a + 2) - (a - 2) * (a + 1) = a ^ 3 + a ^ 2 := by
  have step1 : (a - 1) * (a + 1) = a^2 - 1 := by
    -- Use the distributive property to expand the left side of the equation.
    ring
    -- The `ring` tactic automatically simplifies the expression by expanding and combining like terms.
    -- This step confirms that (a - 1)(a + 1) indeed equals a^2 - 1.
    <;> ring
    <;> ring
    <;> ring
  
  have step2 : (a^2 - 1) * (a + 2) = a^3 + 2*a^2 - a - 2 := by
    -- Expand the given product using distributive property and simplify.
    ring_nf
    <;> linarith [step1]
    <;> linarith [step1]
    <;> linarith [step1]
  
  have step3 : (a - 2) * (a + 1) = a^2 - a - 2 := by
    -- We start with the given equation and simplify it step by step.
    have h1 : (a - 2) * (a + 1) = a^2 - a - 2 := by
      -- Expand the left-hand side using the distributive property.
      ring_nf
    -- The expanded form matches the right-hand side, confirming the identity.
    exact h1
  
  have step4 : (a^3 + 2*a^2 - a - 2) - (a^2 - a - 2) = a^3 + a^2 := by
    -- Simplify the given expressions using algebraic identities and properties.
    simp_all only [mul_add, mul_sub, mul_one, mul_neg, mul_assoc, sub_neg_eq_add, sub_eq_add_neg,
      add_assoc, add_left_comm, add_right_comm]
    -- Use the ring tactic to simplify and verify the final expression.
    ring
  
  have step5 : (a - 1) * (a + 1) * (a + 2) - (a - 2) * (a + 1) = a^3 + a^2 := by
    -- Use the given steps to simplify the expression
    nlinarith [step1, step2, step3, step4]
    <;> ring_nf at step1 step2 step3 step4 ⊢
    <;> nlinarith [step1, step2, step3, step4]
  
  linarith