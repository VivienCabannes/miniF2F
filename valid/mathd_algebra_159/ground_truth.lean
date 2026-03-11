import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_159 (b : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 3 * x ^ 4 - 7 * x ^ 3 + 2 * x ^ 2 - b * x + 1) (h₁ : f 1 = 1) : b = -2 := by
  simp_all only [rpow_two, mul_one, sub_eq_add_neg, add_assoc]
  ring_nf
  linarith