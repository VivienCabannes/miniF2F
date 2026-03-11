import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 (x y z : ℤ)
  (h₀ : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = x * y * z) :
  x + y + z + 6 ∣ x ^ 3 + y ^ 3 + z ^ 3 := by
  have h₁ : (x - y)^2 + (y - z)^2 + (z - x)^2 = 2*(x^2 + y^2 + z^2 - x*y - y*z - z*x) := by
    -- Expand the left side using the distributive property and simplify.
    simp only [sub_sq, add_assoc, add_left_comm, add_comm] at h₀ ⊢
    -- Use linear arithmetic to conclude the proof.
    linarith
  
  have h₂ : 2*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = x * y * z := by
    -- Start with the first equation and expand the left-hand side.
    have h₂ : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 2*(x^2 + y^2 + z^2 - x*y - y*z - z*x) := h₁
    -- Substitute the expanded form into the second equation.
    have h₃ : 2*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = x * y * z := by
      linarith
    -- Conclude the proof by confirming the equality.
    linarith
  
  have h₃ : x^3 + y^3 + z^3 = (x + y + z)^3 - 3*(x + y + z)*(x*y + y*z + z*x) + 3*x*y*z := by
    have h₃ : x ^ 3 + y ^ 3 + z ^ 3 = (x + y + z) ^ 3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * x * y * z := by
      ring
    rw [h₃]
    <;> simp_all
    <;> ring
    <;> linarith
  
  have h₄ : x + y + z + 6 ∣ x^3 + y^3 + z^3 := by
    -- We use the given conditions to simplify and solve for the variables.
    use x^2 + y^2 + z^2 - x*y - y*z - z*x
    -- Normalize the expression by expanding and simplifying it.
    ring_nf
    -- Simplify the expression using specific algebraic rules and properties.
    <;> simp_all only [mul_assoc, mul_comm, mul_left_comm, mul_one, mul_zero, add_assoc, add_left_comm, add_comm]
    -- Use linear arithmetic to verify the divisibility.
    <;> linarith
  
  -- Use the given condition h₄ to conclude the proof
  simpa using h₄