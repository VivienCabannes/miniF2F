import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2009_p5 (x : ℝ) (h₀ : x ^ 3 - (x + 1) * (x - 1) * x = 5) : x ^ 3 = 125 := by
  have h₁ : (x + 1) * (x - 1) * x = x^3 - x := by
    ring_nf at h₀ ⊢
    <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg x]
  
  have h₂ : x^3 - x = x^3 - 5 := by
    -- We start by using the given equations and simplifying the expressions.
    have h₂ : (x + 1) * (x - 1) * x = x^3 - x := by linarith
    -- Using the second equation, we establish that (x + 1)(x - 1)x = x^3 - x.
    -- Now, we need to show that x^3 - x = x^3 - 5.
    -- We use the given equation x^3 - (x + 1)(x - 1)x = 5 and the established equation (x + 1)(x - 1)x = x^3 - x.
    -- By substituting the second equation into the first, we get x^3 - (x^3 - x) = 5.
    -- Simplifying this, we find that x = 5.
    -- With x = 5, we verify that x^3 - x = 5^3 - 5 = 120, which matches the required result.
    linarith
  
  have h₃ : -x = -5 := by
    -- Simplify the equations to find the value of x
    linarith
  
  have h₄ : x = 5 := by
    -- We start with the given equation: x^3 - (x + 1)(x - 1)x = 5
    have h₀ : x ^ 3 - (x + 1) * (x - 1) * x = 5 := h₀
    -- Simplify the expression (x + 1)(x - 1)x
    have h₁ : (x + 1) * (x - 1) * x = x ^ 3 - x := by
      ring
    -- Substitute the simplified expression into the original equation
    rw [h₁] at h₀
    -- Simplify the equation to isolate x
    have h₂ : x ^ 3 - x = x ^ 3 - 5 := by
      linarith
    -- Solve for x by eliminating x^3
    have h₃ : -x = -5 := by
      linarith
    -- Obtain the final solution for x
    have h₄ : x = 5 := by
      linarith
    exact h₄
  
  have h₅ : x^3 = 125 := by
    -- From the fourth hypothesis, we know x = 5.
    have h₅ : x = 5 := by linarith
    -- Substitute x = 5 into the goal.
    subst h₅
    -- Normalize the numerical expression to confirm x^3 = 125.
    norm_num
  
  -- We have already established that x = 5, and we need to show that x^3 = 125.
  have h₆ : x = 5 := h₄
  -- Since x = 5, we can substitute x with 5 in the equation x^3 = 125.
  rw [h₆]
  -- Simplify the equation to confirm that 5^3 = 125.
  norm_num