import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_100
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Nat.gcd n 40 = 10)
  (h₂ : Nat.lcm n 40 = 280) :
  n = 70 := by
  have h₃ : n * 40 = 2800 := by
    have h₃₁ : Nat.gcd n 40 * Nat.lcm n 40 = n * 40 := by
      rw [Nat.gcd_mul_lcm]
    rw [h₁, h₂] at h₃₁
    <;> norm_num at h₃₁ ⊢
    <;> linarith
  
  have h₄ : n = 70 := by
    have h₄₁ : n * 40 = 2800 := h₃
    have h₄₂ : n = 70 := by
      -- Use the fact that n * 40 = 2800 to solve for n
      have h₄₃ : n ≤ 70 := by
        by_contra h
        -- If n > 70, then n * 40 > 2800
        have h₄₄ : n ≥ 71 := by
          omega
        have h₄₅ : n * 40 ≥ 71 * 40 := by
          nlinarith
        have h₄₆ : n * 40 > 2800 := by
          nlinarith
        omega
      have h₄₄ : n ≥ 70 := by
        by_contra h
        -- If n < 70, then n * 40 < 2800
        have h₄₅ : n ≤ 69 := by
          omega
        have h₄₆ : n * 40 ≤ 69 * 40 := by
          nlinarith
        have h₄₇ : n * 40 < 2800 := by
          nlinarith
        omega
      -- Since n ≤ 70 and n ≥ 70, n must be 70
      omega
    exact h₄₂
  
  rw [h₄]
  <;> norm_num
  <;> try linarith