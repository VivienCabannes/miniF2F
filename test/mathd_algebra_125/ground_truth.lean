import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_125
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : 5 * x = y)
  (h₂ : (↑x - (3:ℤ)) + (y - (3:ℤ)) = 30) :
  x = 6 := by
  have h₃ : (x : ℤ) + y = 36 := by
    have h₃₁ : (x : ℤ) - (3 : ℤ) + ((y : ℤ) - (3 : ℤ)) = 30 := by simpa using h₂
    have h₃₂ : (x : ℤ) + (y : ℤ) - 6 = 30 := by
      linarith
    have h₃₃ : (x : ℤ) + (y : ℤ) = 36 := by linarith
    exact_mod_cast h₃₃
  
  have h₄ : x + y = 36 := by
    norm_cast at h₃ ⊢
    <;> omega
  
  have h₅ : x = 6 := by
    have h₅₁ : y = 5 * x := by
      omega
    have h₅₂ : x + y = 36 := h₄
    rw [h₅₁] at h₅₂
    have h₅₃ : x + (5 * x) = 36 := by simpa using h₅₂
    have h₅₄ : 6 * x = 36 := by
      omega
    have h₅₅ : x = 6 := by
      omega
    exact h₅₅
  
  exact h₅