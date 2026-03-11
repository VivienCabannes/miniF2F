import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = 26 := by
  have h₃ : (x + 1) * (y + 1) = 81 := by
    -- Simplify the expression by rearranging the given equation.
    simp only [add_assoc, mul_add, mul_comm, mul_left_comm, mul_assoc] at h₂ ⊢
    -- Use linear arithmetic to verify the equality.
    linarith
  
  have h₄ : (x + 1 = 27 ∧ y + 1 = 3) ∨ (x + 1 = 9 ∧ y + 1 = 9) ∨ (x + 1 = 3 ∧ y + 1 = 27) := by
    have h₄ : x + y + x * y = 80 := h₂
    have h₅ : (x + 1) * (y + 1) = 81 := h₃
    have h₆ : x > y := by linarith
    have h₇ : x ≥ 0 := by linarith
    have h₈ : y ≥ 0 := by linarith
    have h₉ : x ≤ 80 := by nlinarith
    have h₁₀ : y ≤ 80 := by nlinarith
    interval_cases x <;> interval_cases y <;> norm_num at h₅ ⊢ <;> nlinarith
  
  have h₅ : x + 1 = 27 ∧ y + 1 = 3 := by
    -- We need to show that the only valid solution is x + 1 = 27 and y + 1 = 3.
    have h₅ : x + 1 = 27 ∧ y + 1 = 3 := by
      -- We will check each case provided in h₄ to see which one satisfies the conditions.
      rcases h₄ with (⟨h₅, h₆⟩ | ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩)
      -- Case 1: x + 1 = 27 and y + 1 = 3.
      -- This case directly satisfies the conditions, so we return it.
      <;> simp_all
      -- Case 2 and 3: x + 1 = 9 and y + 1 = 9, or x + 1 = 3 and y + 1 = 27.
      -- These cases do not satisfy the condition 0 < y < x, so we discard them.
      <;> omega
    -- Finally, we return the valid solution.
    exact h₅
  
  have h₆ : x = 26 ∧ y = 2 := by
    -- From the given conditions, we have x = 26 and y = 2.
    have h₆ : x = 26 := by linarith
    have h₇ : y = 2 := by linarith
    -- Simplify the final result.
    simp_all
  
  have h₇ : 26 + 2 + 26 * 2 = 80 := by
    -- This step involves verifying the equation holds for the given values of x and y.
    have h₇ : 26 + 2 + 26 * 2 = 80 := by
      -- Use the given conditions to substitute and simplify the equation.
      simp [h₆]
    -- Use the previously derived equation to conclude the proof.
    simp [h₆]
    <;> linarith
  
  -- We already have the solution (x, y) = (26, 2) from the given conditions.
  have h₈ : x = 26 := by
    -- We use the fact that (x + 1)(y + 1) = 81 and the given conditions to solve for x.
    cases' h₅ with h₅_left h₅_right
    -- Solve for x using the given conditions.
    subst_vars
    -- Verify that the solution satisfies the original equation.
    linarith
  -- The solution x = 26 is verified.
  exact h₈