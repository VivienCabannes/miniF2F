import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_11 (a b : ℝ) (h₀ : a ≠ b) (h₁ : a ≠ 2 * b)
    (h₂ : (4 * a + 3 * b) / (a - 2 * b) = 5) : (a + 11 * b) / (a - b) = 2 := by
  have h₃ : a - b ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h₄ : a - 2 * b ≠ 0 := by
    intro h
    apply h₁
    linarith
  -- We need to show that (a + 11 * b) / (a - b) = 2
  field_simp [h₃, h₄, sub_ne_zero, mul_sub] at *
  -- Simplify the given equation (4 * a + 3 * b) / (a - 2 * b) = 5
  linarith