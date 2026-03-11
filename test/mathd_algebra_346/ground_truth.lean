import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_346
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x - 3)
  (h₁ : ∀ x, g x = x + 1) :
  g (f 5 - 1) = 7 := by
  have h₂ : f 5 = 7 := by
    rw [h₀]
    norm_num
  
  have h₃ : f 5 - 1 = 6 := by
    rw [h₂]
    norm_num
  
  have h₄ : g (f 5 - 1) = 7 := by
    rw [h₃]
    rw [h₁]
    <;> norm_num
    <;> linarith
  
  rw [h₄]