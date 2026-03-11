import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1989_p8
  (a b c d e f g : ℝ)
  (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
  (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
  (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
  16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
  have h_sum : a + b + c + d + e + f + g = 50 := by
    have h₃ : 3 * a + 5 * b + 7 * c + 9 * d + 11 * e + 13 * f + 15 * g = 11 := by
      linarith
    have h₄ : 5 * a + 7 * b + 9 * c + 11 * d + 13 * e + 15 * f + 17 * g = 111 := by
      linarith
    have h₅ : 2 * (a + b + c + d + e + f + g) = 100 := by
      linarith
    linarith
  
  have h_T : 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
    have h₃ : 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
      -- Use the linear combination T = S₁ - 3S₂ + 3S₃
      have h₄ : 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) - 3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) + 3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) := by
        ring
      rw [h₄]
      rw [h₀, h₁, h₂]
      <;> linarith
    exact h₃
  
  exact h_T