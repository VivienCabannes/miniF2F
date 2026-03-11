import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  have h₁ : 0 ≤ x := by
    by_contra h
    -- Assume x < 0 and derive a contradiction
    have h₂ : x < 0 := by linarith
    -- Consider the cases x < -1 and -1 ≤ x < 0
    by_cases h₃ : x < -1
    · -- Case: x < -1
      have h₄ : abs (x - 1) = -(x - 1) := by
        rw [abs_of_neg (by linarith)]
        <;> linarith
      have h₅ : abs x = -x := by
        rw [abs_of_neg (by linarith)]
      have h₆ : abs (x + 1) = -(x + 1) := by
        rw [abs_of_neg (by linarith)]
        <;> linarith
      rw [h₄, h₅, h₆] at h₀
      -- Simplify the equation to find x = -1/2, which contradicts x < -1
      have h₇ : - (x - 1) + -x + - (x + 1) = x + 2 := by linarith
      have h₈ : x = -1 / 2 := by linarith
      linarith
    · -- Case: -1 ≤ x < 0
      have h₄ : x ≥ -1 := by linarith
      have h₅ : abs (x - 1) = -(x - 1) := by
        rw [abs_of_neg (by linarith)]
        <;> linarith
      have h₆ : abs x = -x := by
        rw [abs_of_neg (by linarith)]
      have h₇ : abs (x + 1) = x + 1 := by
        rw [abs_of_nonneg (by linarith)]
      rw [h₅, h₆, h₇] at h₀
      -- Simplify the equation to find x = 0, which contradicts x < 0
      have h₈ : - (x - 1) + -x + (x + 1) = x + 2 := by linarith
      have h₉ : x = 0 := by linarith
      linarith
  
  have h₂ : x ≤ 1 := by
    by_contra h
    -- Assume x > 1 and derive a contradiction
    have h₃ : x > 1 := by linarith
    -- Derive the form of each absolute value under x > 1
    have h₄ : abs (x - 1) = x - 1 := by
      rw [abs_of_nonneg (by linarith)]
    have h₅ : abs x = x := by
      rw [abs_of_nonneg (by linarith)]
    have h₆ : abs (x + 1) = x + 1 := by
      rw [abs_of_nonneg (by linarith)]
    -- Substitute back into the original equation
    rw [h₄, h₅, h₆] at h₀
    -- Simplify to find x = 1, which contradicts x > 1
    have h₇ : x = 1 := by linarith
    linarith
  
  have h₃ : 0 ≤ x ∧ x ≤ 1 := by
    exact ⟨h₁, h₂⟩
  
  exact h₃