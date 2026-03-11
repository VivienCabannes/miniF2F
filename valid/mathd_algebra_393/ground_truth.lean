import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_393 (σ : Equiv ℝ ℝ) (h₀ : ∀ x, σ.1 x = 4 * x ^ 3 + 1) : σ.2 33 = 2 := by
  have eq1 : 4 * (σ.2 33) ^ 3 + 1 = 33 := by
    -- Use the definition of the inverse function to express σ.2 33 in terms of σ.
    have h₁ := σ.right_inv 33
    -- Simplify the expression using the given function definition and properties of the inverse function.
    simp_all [Equiv.eq_symm_apply]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have eq2 : 4 * (σ.2 33) ^ 3 = 32 := by
    have h₁ := σ.apply_symm_apply 33
    simp_all [Equiv.eq_symm_apply]
    -- Simplify the equation to isolate the term involving the cube of the inverse function applied to 33.
    <;> ring_nf
    -- Normalize the equation to prepare for solving the remaining arithmetic.
    <;> nlinarith [sq_nonneg (σ.2 33)]
  
  have eq3 : (σ.2 33) ^ 3 = 8 := by
    -- We start by simplifying the equation 4 * (σ.2 33) ^ 3 = 32 to solve for (σ.2 33) ^ 3.
    have h₁ : (σ.2 33) ^ 3 = 8 := by
      -- We use the given equation eq2: 4 * (σ.2 33) ^ 3 = 32.
      apply mul_left_cancel₀ (show (4 : ℝ) ≠ 0 by norm_num)
      -- We simplify the equation to (σ.2 33) ^ 3 = 8.
      linarith
    -- We have already derived that (σ.2 33) ^ 3 = 8, so we can directly use this result.
    rw [h₁]
  
  have eq4 : σ.2 33 = 2 := by
    -- We need to show that the inverse of σ at 33 is 2.
    -- Given the properties of σ and the steps above, we can directly use the fact that the cube of 2 is 8.
    have h₁ : σ.2 33 = 2 := by
      -- Use the fact that the cube of 2 is 8 to solve for the inverse of σ at 33.
      simp_all [Equiv.symm_apply_eq]
      -- Simplify the equation using the given properties and the fact that the cube of 2 is 8.
      <;> nlinarith
    -- The final result is that the inverse of σ at 33 is 2.
    exact h₁
  
  apply eq4