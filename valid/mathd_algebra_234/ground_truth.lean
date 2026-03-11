import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_234 (d : ℝ) (h₀ : 27 / 125 * d = 9 / 25) : 3 / 5 * d ^ 3 = 25 / 9 := by
  have r_eq : d = 5 / 3 := by
    have h₁ : d = 5 / 3 := by
      -- We need to solve for d, so we isolate d by dividing both sides by 27/125
      apply Eq.symm
      -- Simplify the equation by clearing the fractions
      field_simp at h₀ ⊢
      -- Use linear arithmetic to solve for d
      linarith
    -- Substitute the found value of d back into the original equation to verify
    rw [h₁]
  
  have d_cubed : d^3 = 125 / 27 := by
    -- Substitute the given value of d into the equation
    rw [r_eq]
    -- Simplify the expression using field operations
    field_simp
    -- Normalize the expression using ring operations
    ring_nf
    -- Simplify all expressions using given hypotheses
    <;> simp_all
    -- Use linear arithmetic to verify the final result
    <;> linarith
  
  have final_eq : 3 / 5 * d^3 = 25 / 9 := by
    -- We know from the problem statement that 27/125 * d = 9/25. We need to find d.
    have h₁ : 27 / 125 * d = 9 / 25 := h₀
    -- We need to solve for d. We can do this by dividing both sides of the equation by 27/125.
    have h₂ : d = 5 / 3 := r_eq
    -- We need to find d^3. We can do this by cubing d.
    have h₃ : d^3 = 125 / 27 := d_cubed
    -- Now we need to find 3/5 * d^3. We can do this by multiplying 3/5 by d^3.
    field_simp [h₂, h₃]
    -- Simplify the expression to show that 3/5 * d^3 = 25/9.
    ring
  
  -- We know the value of d^3 from the given information.
  have : d ^ 3 = 125 / 27 := d_cubed
  -- Substitute d^3 into the expression 3/5 * d^3.
  have : 3 / 5 * d ^ 3 = 3 / 5 * (125 / 27) := by rw [this]
  -- Simplify the expression to show that it equals 25/9.
  linarith