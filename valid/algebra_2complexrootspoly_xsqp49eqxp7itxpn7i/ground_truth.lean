import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_2complexrootspoly_xsqp49eqxp7itxpn7i (x : ℂ) :
    x ^ 2 + 49 = (x + 7 * Complex.I) * (x + -7 * Complex.I) := by
  have expand_RHS : (x + 7 * Complex.I) * (x + -7 * Complex.I) = x * x + x * (-7 * Complex.I) + (7 * Complex.I) * x + (7 * Complex.I) * (-7 * Complex.I) := by
    -- Simplify the expression using the distributive property and properties of multiplication and addition in the complex numbers.
    simp [mul_add, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    -- Use the ring tactic to simplify the expression and verify the equality.
    <;> ring
    <;> norm_num
    <;> ring
    <;> norm_num
    <;> ring
    <;> norm_num
    <;> ring
    <;> norm_num
  
  have simplify_RHS : x * x + x * (-7 * Complex.I) + (7 * Complex.I) * x + (7 * Complex.I) * (-7 * Complex.I) = x^2 + 49 := by
    -- Simplify the left-hand side by combining like terms.
    simp only [Complex.I_mul_I, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc] at expand_RHS ⊢
    -- Normalize the expression using algebraic rules to simplify it to the right-hand side.
    ring_nf at expand_RHS ⊢
    -- Simplify the expression to match the right-hand side.
    simp_all
    <;> ring_nf
    <;> simp_all
    <;> ring_nf
    <;> simp_all
  
  have final_proof : x ^ 2 + 49 = (x + 7 * Complex.I) * (x + -7 * Complex.I) := by
    rw [eq_comm] at expand_RHS
    rw [eq_comm] at simplify_RHS
    simp_all
  
  -- The final proof is given as an assumption, so we use it directly.
  exact final_proof