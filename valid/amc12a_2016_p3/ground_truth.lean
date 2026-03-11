import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2016_p3 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x, ∀ (y) (_ : y ≠ 0), f x y = x - y * Int.floor (x / y)) :
  f (3 / 8) (-(2 / 5)) = -(1 / 40) := by
  -- Use the given definition of f to compute f(3/8, -2/5)
  have h₁ := h₀ (3 / 8) (-(2 / 5)) (by norm_num)
  -- Simplify the expression using numerical computations
  norm_num at h₁
  -- Use the property of the floor function to simplify further
  <;> simp_all [Int.floor_eq_iff]
  -- Normalize the numerical expressions
  <;> norm_num
  -- Simplify the fractions
  <;> field_simp
  -- Normalize the cast to integers
  <;> norm_cast