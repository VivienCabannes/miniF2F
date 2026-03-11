import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_116 (k x : ℝ) (h₀ : x = (13 - Real.sqrt 131) / 4)
    (h₁ : 2 * x ^ 2 - 13 * x + k = 0) : k = 19 / 4 := by
  have h₂ : 2 * ((13 - Real.sqrt 131) / 4) ^ 2 - 13 * ((13 - Real.sqrt 131) / 4) + k = 0 := by
    -- Substitute the given value of x into the equation and simplify.
    simp [h₀] at h₁ ⊢
    -- Normalize the expression by expanding and simplifying it.
    ring_nf at h₁ ⊢
    -- Simplify the expression using field operations.
    field_simp at h₁ ⊢
    -- Normalize the expression again to achieve the final simplified form.
    ring_nf at h₁ ⊢
    -- Use linear arithmetic to conclude the proof.
    linarith
  
  have h₃ : 2 * ((13 - Real.sqrt 131) / 4) ^ 2 - 13 * ((13 - Real.sqrt 131) / 4) + k = 0 := by
    -- Normalize the numbers to ensure they are in the correct form.
    norm_num at h₀
    -- Substitute the value of x from h₀ into the equation.
    rw [h₀] at h₁
    -- Normalize the expression by expanding and simplifying it.
    ring_nf at h₁
    -- Use linear arithmetic to verify the equation.
    linarith
  
  have h₄ : k = 19 / 4 := by
    -- Normalize the numbers to simplify the expressions.
    norm_num at *
    -- Expand and simplify the equation using ring operations.
    ring_nf at *
    -- Clear denominators by multiplying through by开孔.
    field_simp at *
    -- Normalize the numbers again to simplify the expressions.
    norm_num at *
    -- Solve the resulting linear equation using arithmetic.
    linarith
  
  -- We already have the value of k from the given information.
  have h₅ : k = 19 / 4 := h₄
  -- Simplify the goal using the known value of k.
  simp_all