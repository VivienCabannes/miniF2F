import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_400
  (x : ℝ)
  (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) :
  x = 50 := by
  have h₁ : x = 50 := by
    have h₂ : x = 50 := by
      -- Simplify the left side: 5 + 500 / 100 * 10 = 55
      -- The equation becomes 55 = (110 / 100) * x
      -- Multiply both sides by 100 to get 5500 = 110 * x
      -- Divide both sides by 110 to get x = 50
      apply_fun (fun x => x * 100) at h₀
      -- Now the equation is (5 + 500 / 100 * 10) * 100 = (110 / 100 * x) * 100
      ring_nf at h₀ ⊢
      -- Simplify the equation to 5500 = 110 * x
      linarith
    exact h₂
  exact h₁