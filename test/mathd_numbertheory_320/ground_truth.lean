import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_320
  (n : ℕ)
  (h₀ : n < 101)
  (h₁ : 101 ∣ (123456 - n)) :
  n = 34 := by
  have h₂ : 123456 % 101 = 34 := by
    norm_num
    <;> rfl
  
  have h₃ : n % 101 = 34 := by
    have h₄ : (123456 - n) % 101 = 0 := by
      exact Nat.mod_eq_zero_of_dvd h₁
    have h₅ : (123456 % 101) = 34 := h₂
    have h₆ : (123456 - n) % 101 = (123456 % 101 - n % 101) % 101 := by
      have h₇ : (123456 - n) % 101 = (123456 % 101 - n % 101) % 101 := by
        omega
      exact h₇
    rw [h₆] at h₄
    have h₇ : (123456 % 101 - n % 101) % 101 = 0 := h₄
    have h₈ : (34 - n % 101) % 101 = 0 := by
      simpa [h₅] using h₇
    have h₉ : n % 101 = 34 := by
      have h₁₀ : n % 101 < 101 := Nat.mod_lt n (by norm_num)
      have h₁₁ : 34 - n % 101 = 0 := by
        by_contra h
        have h₁₂ : 34 - n % 101 > 0 := by
          have h₁₃ : 34 - n % 101 ≠ 0 := h
          have h₁₄ : 34 - n % 101 > 0 := by
            by_contra h₁₅
            have h₁₆ : 34 - n % 101 = 0 := by omega
            contradiction
          exact h₁₄
        have h₁₅ : (34 - n % 101) % 101 = 34 - n % 101 := by
          apply Nat.mod_eq_of_lt
          omega
        rw [h₁₅] at h₈
        omega
      omega
    exact h₉
  
  have h₄ : n = 34 := by
    have h₅ : n % 101 = n := by
      apply Nat.mod_eq_of_lt
      exact h₀
    rw [h₅] at h₃
    omega
  
  exact h₄