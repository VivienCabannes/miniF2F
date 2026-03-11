import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_22 : Real.logb (5 ^ 2) (5 ^ 4) = 2 := by
  -- Simplify the given logarithmic expression using properties of logarithms and exponents.
  simp [Real.logb, div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one,
    show (5 : ℝ) ≠ 0 by norm_num, show (4 : ℝ) ≠ 0 by norm_num,
    show (2 : ℝ) ≠ 0 by norm_num]
  -- Normalize the numerical expressions to confirm the equality.
  <;> norm_num
  <;> ring
  <;> norm_num
  <;> field_simp
  <;> norm_num