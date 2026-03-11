import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_711
  (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 8)
  (h₂ : Nat.lcm m n = 112) :
  72 ≤ m + n := by
  have h₃ : m * n = 896 := by
    have h₃₁ : Nat.gcd m n * Nat.lcm m n = m * n := by
      rw [Nat.gcd_mul_lcm]
    rw [h₁, h₂] at h₃₁
    norm_num at h₃₁ ⊢
    <;> nlinarith
  
  have h₄ : m ∣ 112 := by
    have h₄₁ : m ∣ Nat.lcm m n := Nat.dvd_lcm_left m n
    rw [h₂] at h₄₁
    exact h₄₁
  
  have h₅ : 8 ∣ m := by
    have h₅₁ : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
    rw [h₁] at h₅₁
    exact h₅₁
  
  have h₆ : m = 8 ∨ m = 16 ∨ m = 56 ∨ m = 112 := by
    have h₆₁ : m ∣ 112 := h₄
    have h₆₂ : 8 ∣ m := h₅
    have h₆₃ : m > 0 := by linarith
    have h₆₄ : m ≤ 112 := Nat.le_of_dvd (by norm_num) h₆₁
    -- We now know that m is a multiple of 8 and a divisor of 112.
    -- We can list all multiples of 8 that are divisors of 112 and check which ones are possible.
    have h₆₅ : m = 8 ∨ m = 16 ∨ m = 56 ∨ m = 112 := by
      interval_cases m <;> norm_num at h₆₁ h₆₂ h₆₃ ⊢ <;>
        (try omega) <;> (try norm_num) <;> (try omega)
      <;> (try
        {
          exfalso
          -- For each impossible case, we derive a contradiction.
          have h₆₆ : n ≤ 896 := by
            nlinarith
          interval_cases n <;> norm_num at h₃ h₁ h₂ h₆₁ h₆₂ h₆₃ ⊢ <;>
            (try omega) <;> (try norm_num) <;> (try omega)
          <;> (try
            {
              exfalso
              -- For each impossible case, we derive a contradiction.
              omega
            })
        })
    exact h₆₅
  
  have h₇ : 72 ≤ m + n := by
    rcases h₆ with (rfl | rfl | rfl | rfl)
    · -- Case m = 8
      have h₇₁ : n = 112 := by
        have h₇₂ : 8 * n = 896 := by
          norm_num [h₃] at *
          <;> nlinarith
        nlinarith
      rw [h₇₁]
      <;> norm_num
    · -- Case m = 16
      have h₇₁ : n = 56 := by
        have h₇₂ : 16 * n = 896 := by
          norm_num [h₃] at *
          <;> nlinarith
        nlinarith
      rw [h₇₁]
      <;> norm_num
    · -- Case m = 56
      have h₇₁ : n = 16 := by
        have h₇₂ : 56 * n = 896 := by
          norm_num [h₃] at *
          <;> nlinarith
        nlinarith
      rw [h₇₁]
      <;> norm_num
    · -- Case m = 112
      have h₇₁ : n = 8 := by
        have h₇₂ : 112 * n = 896 := by
          norm_num [h₃] at *
          <;> nlinarith
        nlinarith
      rw [h₇₁]
      <;> norm_num
  exact h₇