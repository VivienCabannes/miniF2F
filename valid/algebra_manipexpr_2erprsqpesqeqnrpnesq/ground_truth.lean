import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_manipexpr_2erprsqpesqeqnrpnesq (e r : ℂ) :
  2 * (e * r) + (e ^ 2 + r ^ 2) = (-r + -e) ^ 2 := by
  have step1 : (-r + -e) ^ 2 = (r + e) ^ 2 := by
    -- Use the property of squares to show that the square of a sum is equal to the square of a difference with negated terms.
    simp only [add_comm, add_left_comm]
    -- Simplify the expression using algebraic identities to show the equality.
    ring
    -- Simplify further using the property of squares and associativity of addition.
    <;> simp only [sq]
    <;> ring
  
  have step2 : (r + e) ^ 2 = r ^ 2 + 2 * (e * r) + e ^ 2 := by
    simp only [add_sq, mul_add, mul_comm, mul_left_comm, mul_assoc, neg_add_rev, neg_sq, neg_mul,
      neg_mul, neg_neg] at step1
    linear_combination step1
  
  have step3 : r ^ 2 + 2 * (e * r) + e ^ 2 = 2 * (e * r) + (e ^ 2 + r ^ 2) := by
    -- Simplify the equation using the commutative property of multiplication
    simp only [mul_comm e r] at step2
    -- Use linear combination to rearrange the terms and show the desired equality
    linear_combination step2
  
  have step4 : 2 * (e * r) + (e ^ 2 + r ^ 2) = (-r + -e) ^ 2 := by
    -- Simplify the expression using the given steps
    simp_all [pow_two, add_mul, mul_add, mul_comm, mul_left_comm]
    -- Use the ring tactic to simplify and verify the equation
    <;> ring
  
  -- We start by using the given equalities to establish the desired result.
  apply step4