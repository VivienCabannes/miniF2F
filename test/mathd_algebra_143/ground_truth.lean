import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_143
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 1)
  (h₁ : ∀ x, g x = x^2 + 3) :
  f (g 2) = 8 := by
  have h₂ : g 2 = 7 := by
    rw [h₁]
    norm_num
  
  have h₃ : f (g 2) = 8 := by
    rw [h₂]
    rw [h₀]
    <;> norm_num
  
  exact h₃