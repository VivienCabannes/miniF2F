import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_2at2pclta2c2p41pc (a c : ℝ) :
  2 * a * (2 + c) ≤ a ^ 2 + c ^ 2 + 4 * (1 + c) := by
  have step1 : 2 * a * (2 + c) = 4 * a + 2 * a * c := by
    -- Use the distributive property to expand the left-hand side.
    simp only [mul_add, mul_comm, mul_left_comm, mul_assoc]
    -- Simplify the expression to match the right-hand side.
    ring
  
  have step2 : a ^ 2 + c ^ 2 + 4 * (1 + c) = a ^ 2 + c ^ 2 + 4 + 4 * c := by
    -- Simplify the expression using basic algebraic identities and properties.
    simp_all only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm,
      add_comm]
    -- Use the ring tactic to simplify the expression further.
    ring
  
  have step3 : 4 * a + 2 * a * c ≤ a ^ 2 + c ^ 2 + 4 + 4 * c := by
    have h : 0 ≤ (a - c) ^ 2 - 4 * (a - c) + 4 := by
      -- Show that the expression (a - c)^2 - 4(a - c) + 4 is non-negative
      have : 0 ≤ (a - c - 2) ^ 2 := sq_nonneg (a - c - 2)
      -- Expand and simplify the expression to match the form of the perfect square
      nlinarith [sq_nonneg (a - c - 2)]
    -- Use the non-negativity of the perfect square to conclude the inequality
    linarith [sq_nonneg (a - c - 2)]
  
  have step4 : 0 ≤ a ^ 2 + c ^ 2 + 4 + 4 * c - 4 * a - 2 * a * c := by
    nlinarith [sq_nonneg (a - c - 2), sq_nonneg (a - 2), sq_nonneg (c - 2),
      sq_nonneg (a + c - 2), sq_nonneg (a + c - 1), sq_nonneg (a + c + 1)]
  
  have step5 : a ^ 2 - 4 * a = (a - 2) ^ 2 - 4 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a - c), sq_nonneg (c - 2)]
  
  have step6 : c ^ 2 + 4 * c = (c + 2) ^ 2 - 4 := by
    -- We use the given inequality step5 to prove the desired result.
    have h₀ : a ^ 2 - 4 * a = (a - 2) ^ 2 - 4 := step5
    -- Simplify the expression on the right-hand side of step5.
    have h₁ : a ^ 2 - 4 * a + 4 = (a - 2) ^ 2 := by linarith
    -- Use the simplified expression to prove the final result.
    have h₂ : c ^ 2 + 4 * c = (c + 2) ^ 2 - 4 := by linarith
    -- The final result follows directly from the simplified expression.
    exact h₂
  
  have step7 : 0 ≤ (a - 2) ^ 2 - 4 + (c + 2) ^ 2 - 4 + 4 - 2 * a * c := by
    -- Combine the results from the previous steps to prove the inequality.
    nlinarith [step1, step2, step3, step4, step5, step6, sq_nonneg (a - 2), sq_nonneg (c + 2), sq_nonneg (a - 2 + c + 2)]
  
  have step8 : 0 ≤ (a - 2) ^ 2 + (c + 2) ^ 2 - 2 * a * c - 4 := by
    -- Use the fact that the square of any real number is non-negative to establish the inequality.
    linarith [sq_nonneg (a - 2 + c + 2), sq_nonneg (a - 2 - c - 2), step5, step6, step7]
  
  -- Using the given steps, we can conclude the proof by linear arithmetic.
  linarith [step1, step2, step3, step4, step5, step6, step7, step8]