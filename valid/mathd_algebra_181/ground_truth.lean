import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_181 (n : ℝ) (h₀ : n ≠ 3) (h₁ : (n + 5) / (n - 3) = 2) : n = 11 := by
  have cross_multiplied : n + 5 = 2 * (n - 3) := by
    have h₂ : n - 3 ≠ 0 := by
      intro H
      rw [sub_eq_zero] at H
      apply h₀
      linarith
    field_simp [h₂] at h₁
    linarith
  
  have expanded : n + 5 = 2 * n - 6 := by
    -- Simplify the equation by cross-multiplying and eliminating the fraction
    field_simp [h₀, sub_ne_zero] at h₁ ⊢
    -- Use linear arithmetic to solve for n
    linarith
  
  have simplified : n - 2 * n = -6 - 5 := by
    -- Given the equation (n + 5) / (n - 3) = 2, we cross-multiply to get n + 5 = 2 * (n - 3)
    have h₂ : n + 5 = 2 * (n - 3) := by linarith
    -- We then simplify the equation to n + 5 = 2n - 6
    have h₃ : n + 5 = 2 * n - 6 := by linarith
    -- Solving for n, we get n = 11
    have h₄ : n = 11 := by linarith
    -- Substituting n = 11 into the original equation to verify, we find that it satisfies the equation
    linarith
  
  have isolated_n : -n = -11 := by
    -- Start with the given equation and cross-multiply to eliminate the fraction.
    have h₀' : n + 5 = 2 * (n - 3) := by linarith
    -- Expand and simplify the equation to isolate n.
    have h₁' : n + 5 = 2 * n - 6 := by linarith
    -- Further simplify to find the value of n.
    have h₂ : n - 2 * n = -6 - 5 := by linarith
    -- Solve for n and verify the result.
    linarith
  
  have solution : n = 11 := by
    -- From the given, we know that n - 2 * n = -6 - 5
    have h₂ : n - 2 * n = -6 - 5 := by linarith
    -- Simplify the equation to get -n = -11
    have h₃ : -n = -11 := by linarith
    -- Solve for n by multiplying both sides by -1
    have h₄ : n = 11 := by linarith
    linarith
  
  have verification : (11 + 5) / (11 - 3) = 2 := by
    -- Normalize the numbers to ensure the arithmetic is correct.
    norm_num [h₀]
    -- Use linear arithmetic to verify the solution.
    <;> linarith
    -- Normalize the numbers again to ensure the final result is correct.
    <;> norm_num
    -- Use linear arithmetic to confirm the solution.
    <;> linarith
  
  -- We have already derived that n = 11, so we can directly use this result.
  have h₂ : n = 11 := solution
  -- Since h₂ states that n = 11, we can conclude the proof by exact application.
  exact h₂