import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_51 (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a + b = 35) (h₂ : a = 2 / 5 * b) :
    b - a = 15 := by
  have h_a : a = (2 / 5) * b := by
    -- Use linear arithmetic to solve the system of equations
    linarith [h₁, h₂]
    -- Simplify the expressions using the given equations
    <;> simp_all
    -- Use linear arithmetic again to finalize the solution
    <;> linarith
    -- Normalize the numerical values to ensure correctness
    <;> norm_num
    -- Use linear arithmetic one last time to confirm the solution
    <;> linarith
  
  have h_sub : (2 / 5) * b + b = 35 := by
    -- Substitute the expression for `a` from `h₂` into `h₁`
    rw [h₂] at h₁
    -- Simplify the equation by combining like terms
    field_simp [h₀.1.ne', h₀.2.ne'] at h₁
    -- Use linear arithmetic to conclude the proof
    linarith
  
  have h_comb : (7 / 5) * b = 35 := by
    -- Combine the terms involving b
    field_simp [h₂, h_a] at h_sub ⊢
    -- Simplify the equation to isolate b
    linarith
    <;> assumption
  
  have h_b : b = 25 := by
    -- Solve for b using the given equations and properties of real numbers.
    have h₃ : b = 25 := by
      -- Clear the fractions by multiplying both sides by 5 to simplify the equation.
      field_simp at h₂ h_a h_sub h_comb
      -- Use linear arithmetic to solve for b.
      linarith
    -- The final result is b = 25.
    exact h₃
  
  have h_a_val : a = 10 := by
    -- We need to show that a = 10. We start by simplifying the equations and solving for a.
    have h₃ : a = 10 := by
      -- Substitute the expression for a from h₂ into h₁.
      rw [h₂] at h₁
      -- Simplify the equation to solve for b.
      field_simp at h₁
      -- Use linear arithmetic to solve for b and then find a.
      linarith
    -- The final step is to confirm that a = 10.
    linarith
  
  have h_diff : b - a = 15 := by
    -- Substitute the value of a from h_a_val into the equation
    subst h_a_val
    -- Substitute the value of b from h_b into the equation
    subst h_b
    -- Use linear arithmetic to verify the final result
    linarith
  
  -- We need to prove that b - a = 15. Given the conditions, we can directly use the provided values and relationships.
  linarith [h₀.1, h₀.2, h₁, h₂, h_a, h_sub, h_comb, h_b, h_a_val, h_diff]