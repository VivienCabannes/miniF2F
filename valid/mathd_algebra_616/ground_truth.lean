import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_616 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 3 + 2 * x + 1)
    (h₁ : ∀ x, g x = x - 1) : f (g 1) = 1 := by
  have g1_eq : g 1 = 1 - 1 := by
    simp [h₁]
    -- Simplify the expression using the definition of g(x)
    -- g(1) = 1 - 1 = 0
    <;> norm_num
    -- Normalize the numerical expression to confirm the result
    -- 1 - 1 = 0
    <;> simp_all
    -- Simplify all expressions to ensure consistency and correctness
    <;> norm_num
    -- Normalize numerical expressions again to confirm the result
    <;> linarith
  
  have g1_eq_zero : g 1 = 0 := by
    -- Simplify the expression using the definitions of f and g
    simp_all only [rpow_two, mul_neg, mul_one, sub_eq_add_neg, add_assoc]
    -- Normalize the numerical expression to confirm the result
    norm_num
  
  have fg1_eq : f (g 1) = f 0 := by
    -- Simplify the goal using the given definitions and properties.
    simp_all only [rpow_two, mul_one, mul_zero, sub_zero, sub_eq_add_neg, neg_add_rev, neg_neg, neg_zero,
      add_zero, zero_add, zero_mul, mul_zero, add_left_neg, add_right_neg, zero_sub, sub_zero, sub_neg_eq_add,
      add_comm, add_left_comm, add_assoc]
    -- Normalize the numerical expressions to confirm the result.
    <;> norm_num
  
  have f0_eq : f 0 = 0 ^ 3 + 2 * 0 + 1 := by
    -- Simplify the goal using the given function definitions
    simp_all only [h₀, h₁, mul_zero, mul_one, sub_zero, zero_add]
    -- Normalize the numerical expressions
    <;> norm_num
    <;> linarith
  
  have f0_eq_one : f 0 = 1 := by
    -- Simplify the goal using the given definitions and properties of addition and multiplication.
    simp_all [h₀, h₁, g1_eq, g1_eq_zero, fg1_eq, f0_eq]
    -- <;> linarith
  
  have final_eq : f (g 1) = 1 := by
    -- Simplify the goal using the given definitions and properties.
    simp_all
    -- Use linear arithmetic to confirm the final result.
    <;> linarith
  
  -- Using the definitions of f and g, simplify the expression f(g(1))
  simp_all only [rpow_two, mul_one, mul_zero, add_zero, sub_self, zero_add]
  -- Verify the final result using linear arithmetic
  <;> linarith