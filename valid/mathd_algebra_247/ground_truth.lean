import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_247 (t s : ℝ) (n : ℤ) (h₀ : t = 2 * s - s ^ 2) (h₁ : s = n ^ 2 - 2 ^ n + 1)
  (_ : n = 3) : t = 0 := by
  subst n
  -- Substitute n = 3 into the equation for s
  simp [h₁, h₀, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod]
  -- Simplify the expression using the substituted values and algebraic properties
  -- Verify that the simplified expression equals 0 when n = 3
  <;> norm_num
  -- Use norm_num to confirm the numerical result
  <;> ring
  -- Use ring to confirm the algebraic result
  <;> nlinarith