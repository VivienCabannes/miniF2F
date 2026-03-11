import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_110 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ b ≤ a) (h₁ : (a + b) % 10 = 2)
  (h₂ : (2 * a + b) % 10 = 1) : (a - b) % 10 = 6 := by
  have h₃ : (a) % 10 = 9 := by
    have h₃ := congr_arg (· % 10) h₁
    have h₄ := congr_arg (· % 10) h₂
    have h₅ := congr_arg (· % 10) h₁
    simp at h₃ h₄ h₅
    omega
  
  have h₄ : (b) % 10 = 3 := by
    have h₄ := congr_arg (· % 10) h₁
    have h₅ := congr_arg (· % 10) h₂
    have h₆ := congr_arg (· % 10) h₃
    simp at h₄ h₅ h₆
    omega
  
  have h₅ : (a - b) % 10 = 6 := by
    have a_mod_10 : a % 10 = 9 := h₃
    have b_mod_10 : b % 10 = 3 := h₄
    have a_minus_b_mod_10 : (a - b) % 10 = 6 := by
      -- Use the given conditions and properties of modular arithmetic to derive the result.
      omega
    exact a_minus_b_mod_10
  
  -- We use the given conditions to derive the result.
  have := h₅
  -- Simplify the context by using the given conditions.
  simp_all [h₀, h₁, h₂, h₃, h₄]