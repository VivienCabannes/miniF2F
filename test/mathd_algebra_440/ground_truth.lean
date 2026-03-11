import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_440
  (x : ℝ)
  (h₀ : 3 / 2 / 3 = x / 10) :
  x = 5 := by
  have h₁ : x = 5 := by
    have h₂ : x = 5 := by
      -- Simplify the equation using norm_num to handle the division and multiplication.
      norm_num at h₀ ⊢
      <;>
      (try ring_nf at h₀ ⊢) <;>
      (try linarith) <;>
      (try nlinarith) <;>
      (try field_simp at h₀ ⊢) <;>
      (try ring_nf at h₀ ⊢) <;>
      (try linarith) <;>
      (try nlinarith)
      <;>
      linarith
    exact h₂
  exact h₁