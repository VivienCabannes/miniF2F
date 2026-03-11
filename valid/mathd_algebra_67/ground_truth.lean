import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_67 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 3) (h₁ : ∀ x, g x = x ^ 2 - 2) :
    g (f (-1)) = 2 := by
  have hf_minus1 : f (-1) = 5 * (-1) + 3 := by
    simp_all
    -- Simplify the expressions using the given functions and properties of multiplication and addition.
    <;> ring
    -- Use the ring tactic to simplify the algebraic expressions and verify the equality.
    <;> norm_num
    -- Normalize the numerical expressions to confirm the correctness of the result.
    <;> linarith
  
  have f_minus1_value : f (-1) = -2 := by
    -- Simplify the given expressions and assumptions using algebraic identities and properties.
    simp_all only [rpow_two, mul_neg, mul_one, mul_add, mul_sub, mul_comm, mul_left_comm,
      mul_assoc, sub_eq_add_neg, add_assoc]
    -- Use linear arithmetic to solve the resulting equations.
    <;> linarith
  
  have hg_minus2 : g (-2) = (-2) ^ 2 - 2 := by
    -- Simplify the goal using the given function definitions and properties.
    simp_all only [h₀, h₁, mul_neg, mul_one, mul_add, mul_sub, mul_comm]
    -- Normalize the numerical expressions to verify the result.
    <;> norm_num
  
  have g_minus2_value : g (-2) = 2 := by
    -- Simplify the goal using the definition of g(x)
    simp_all only [rpow_two, mul_neg, mul_one, mul_add, mul_sub, mul_comm]
    -- Use linear arithmetic to verify the simplified equation
    linarith
  
  have final_result : g (f (-1)) = 2 := by
    -- We need to show that g(f(-1)) = 2.
    -- Given f(-1) = -2 and g(-2) = 2, we can directly conclude g(f(-1)) = g(-2) = 2.
    rw [f_minus1_value]
    -- Now we substitute f(-1) with -2 in the expression g(f(-1)).
    rw [g_minus2_value]
  
  -- We use the given definitions of f and g to compute the values required.
  simp_all only [rpow_two, mul_neg, mul_one, mul_zero, mul_neg_one, mul_comm]
  -- Simplify the expressions to verify the final result.
  <;> linarith