import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_113
  (x : ℝ) :
  x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by
  have h₀ : (x - 7) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (x - 7)]
    -- We use `nlinarith` to prove that the square of any real number is non-negative.
    -- The lemma `sq_nonneg (x - 7)` directly states that `(x - 7)^2 ≥ 0`, which is trivially true.
    <;>
    linarith
  
  have h₁ : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
    have h₂ : x ^ 2 - 14 * x + 3 - (7 ^ 2 - 14 * 7 + 3) = (x - 7) ^ 2 := by
      ring_nf
      <;>
      nlinarith
    have h₃ : x ^ 2 - 14 * x + 3 - (7 ^ 2 - 14 * 7 + 3) ≥ 0 := by
      linarith
    linarith
  
  exact h₁