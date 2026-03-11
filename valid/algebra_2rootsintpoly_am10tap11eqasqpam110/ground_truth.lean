import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_2rootsintpoly_am10tap11eqasqpam110 (a : ℂ) :
    (a - 10) * (a + 11) = a ^ 2 + a - 110 := by
  have step1 : (a - 10) * (a + 11) = a * a + a * 11 - 10 * a - 10 * 11 := by
    -- Use the distributive property to expand the product of the two binomials.
    simp only [mul_add, mul_sub, mul_one, mul_neg, mul_comm]
    -- Combine like terms to simplify the expression.
    ring
    <;> ring
    <;> ring
    <;> ring
  
  have step2 : a * a + a * 11 - 10 * a - 10 * 11 = a^2 + (11 * a - 10 * a) - 110 := by
    -- We use the given equation to simplify the left-hand side to the desired form on the right-hand side.
    rw [eq_comm] at step1
    -- We use linear arithmetic to confirm the equivalence.
    linear_combination step1
  
  have step3 : a^2 + (11 * a - 10 * a) - 110 = a^2 + a - 110 := by
    simp_all only [sub_mul, add_mul, mul_add, mul_sub, mul_one, mul_neg, mul_comm]
    <;> ring
    <;> simp_all only [mul_comm]
    <;> ring
  
  -- Combine the given steps to simplify the expression
  have h : (a - 10) * (a + 11) = a ^ 2 + a - 110 := by
    rw [step1]  -- Apply the first step
    rw [step2]  -- Apply the second step
    rw [step3]  -- Apply the third step
  -- The final result follows from the combined steps
  exact h