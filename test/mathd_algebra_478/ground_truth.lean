import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_478
  (b h v : ℝ)
  (h₀ : 0 < b ∧ 0 < h ∧ 0 < v)
  (h₁ : v = 1 / 3 * (b * h))
  (h₂ : b = 30)
  (h₃ : h = 13 / 2) :
  v = 65 := by
  have h₄ : v = 65 := by
    rw [h₁, h₂, h₃]
    -- Substitute b = 30 and h = 13 / 2 into the equation for v
    norm_num [mul_assoc]
    <;> ring_nf at *
    <;> norm_num at *
    <;> linarith
  exact h₄