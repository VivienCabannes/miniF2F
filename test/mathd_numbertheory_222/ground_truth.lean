import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_222
  (b : ℕ)
  (h₀ : Nat.lcm 120 b = 3720)
  (h₁ : Nat.gcd 120 b = 8) :
  b = 248 := by
  have h₂ : 120 * b = 29760 := by
    have h₂₁ : Nat.gcd 120 b * Nat.lcm 120 b = 120 * b := by
      rw [Nat.gcd_mul_lcm]
    rw [h₁, h₀] at h₂₁
    <;> norm_num at h₂₁ ⊢
    <;> linarith
  
  have h₃ : b = 248 := by
    have h₄ : b = 248 := by
      have h₅ : 120 * b = 29760 := h₂
      have h₆ : b = 248 := by
        -- Use the fact that 120 * b = 29760 to solve for b
        have h₇ : b ≤ 248 := by
          by_contra h
          -- If b > 248, then 120 * b > 29760
          have h₈ : b ≥ 249 := by
            omega
          have h₉ : 120 * b ≥ 120 * 249 := by
            exact Nat.mul_le_mul_left 120 h₈
          have h₁₀ : 120 * 249 = 29880 := by norm_num
          have h₁₁ : 120 * b ≥ 29880 := by
            linarith
          have h₁₂ : 120 * b > 29760 := by
            omega
          omega
        -- Use the fact that b ≤ 248 to narrow down the possibilities
        interval_cases b <;> norm_num at h₅ ⊢ <;> try omega
      exact h₆
    exact h₄
  
  exact h₃