import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_495
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a % 10 = 2)
  (h₂ : b % 10 = 4)
  (h₃ : Nat.gcd a b = 6) :
  108 ≤ Nat.lcm a b := by
  have h₄ : 12 ≤ a := by
    by_contra h
    have h₅ : a ≤ 11 := by linarith
    have h₆ : a % 10 = 2 := h₁
    have h₇ : 6 ∣ a := by
      have h₇₁ : Nat.gcd a b = 6 := h₃
      have h₇₂ : 6 ∣ a := by
        have h₇₃ : 6 ∣ Nat.gcd a b := by simp [h₃]
        exact Nat.dvd_trans h₇₃ (Nat.gcd_dvd_left a b)
      exact h₇₂
    interval_cases a <;> norm_num at h₆ h₇ ⊢ <;> omega

  have h₅ : 24 ≤ b := by
    by_contra h
    have h₅₁ : b ≤ 23 := by linarith
    have h₅₂ : b % 10 = 4 := h₂
    have h₅₃ : 6 ∣ b := by
      have h₅₄ : 6 ∣ Nat.gcd a b := by simp [h₃]
      have h₅₅ : 6 ∣ b := by
        have h₅₅₁ : 6 ∣ Nat.gcd a b := h₅₄
        have h₅₅₂ : 6 ∣ b := Nat.dvd_trans h₅₅₁ (Nat.gcd_dvd_right a b)
        exact h₅₅₂
      exact h₅₅
    interval_cases b <;> norm_num at h₅₂ h₅₃ ⊢ <;> omega

  have h₆ : a ≠ 0 := by linarith

  have h₇ : b ≠ 0 := by linarith

  have h₈ : a * b = 6 * Nat.lcm a b := by
    have h₈₁ : Nat.gcd a b = 6 := h₃
    have h₈ : a * b = Nat.gcd a b * Nat.lcm a b := by
      rw [Nat.gcd_mul_lcm]
    rw [h₈₁] at h₈
    <;> linarith

  have h₉ : a = 12 → 54 ≤ b := by
    intro h₉₁
    by_contra h₉₂
    have h₉₃ : b ≤ 53 := by linarith
    have h₉₄ : 6 ∣ b := by
      have h₉₅ : 6 ∣ Nat.gcd a b := by simp [h₃]
      have h₉₆ : 6 ∣ b := by
        have h₉₆₁ : 6 ∣ Nat.gcd a b := h₉₅
        have h₉₆₂ : 6 ∣ b := Nat.dvd_trans h₉₆₁ (Nat.gcd_dvd_right a b)
        exact h₉₆₂
      exact h₉₆
    have h₉₅ : b % 10 = 4 := h₂
    have h₉₆ : a = 12 := h₉₁
    have h₉₇ : Nat.gcd a b = 6 := h₃
    have h₉₈ : a = 12 := h₉₁
    have h₉₉ : Nat.gcd 12 b = 6 := by simpa [h₉₈] using h₃
    interval_cases b <;> norm_num [Nat.gcd_eq_right, Nat.gcd_eq_left] at h₉₄ h₉₅ h₉₉ ⊢ <;>
      (try omega) <;> (try contradiction) <;> (try nlinarith)

  have h₁₀ : a = 12 → 648 ≤ a * b := by
    intro h₁₀₁
    have h₁₀₂ : 54 ≤ b := h₉ h₁₀₁
    have h₁₀₃ : a = 12 := h₁₀₁
    have h₁₀₄ : a * b ≥ 12 * 54 := by
      calc
        a * b = 12 * b := by rw [h₁₀₃]
        _ ≥ 12 * 54 := by
          have h₁₀₅ : 54 ≤ b := h₁₀₂
          nlinarith
        _ = 12 * 54 := by ring
    nlinarith

  have h₁₁ : a > 12 → 42 ≤ a := by
    intro h₁₁₁
    have h₁₁₂ : a ≥ 12 := by linarith
    have h₁₁₃ : a % 10 = 2 := h₁
    have h₁₁₄ : 6 ∣ a := by
      have h₁₁₅ : 6 ∣ Nat.gcd a b := by simp [h₃]
      have h₁₁₆ : 6 ∣ a := by
        have h₁₁₆₁ : 6 ∣ Nat.gcd a b := h₁₁₅
        have h₁₁₆₂ : 6 ∣ a := Nat.dvd_trans h₁₁₆₁ (Nat.gcd_dvd_left a b)
        exact h₁₁₆₂
      exact h₁₁₆
    -- We need to show that if a > 12 and a ≡ 2 mod 10 and 6 ∣ a, then a ≥ 42.
    -- We will use contradiction to prove this.
    by_contra h₁₁₅
    have h₁₁₆ : a < 42 := by linarith
    have h₁₁₇ : a > 12 := h₁₁₁
    -- We will check all possible values of a between 12 and 42 that satisfy the conditions.
    have h₁₁₈ : a ≤ 41 := by linarith
    interval_cases a <;> norm_num at h₁₁₃ h₁₁₄ ⊢ <;> omega

  have h₁₂ : a > 12 → 1008 ≤ a * b := by
    intro h₁₂₁
    have h₁₂₂ : 42 ≤ a := h₁₁ h₁₂₁
    have h₁₂₃ : 24 ≤ b := h₅
    have h₁₂₄ : a * b ≥ 42 * 24 := by
      nlinarith
    nlinarith

  have h₁₃ : 648 ≤ a * b := by
    by_cases h₁₃₁ : a = 12
    · have h₁₃₂ : 648 ≤ a * b := h₁₀ h₁₃₁
      exact h₁₃₂
    · have h₁₃₃ : a > 12 := by
        by_contra h₁₃₄
        have h₁₃₅ : a ≤ 12 := by linarith
        have h₁₃₆ : a ≥ 12 := h₄
        have h₁₃₇ : a = 12 := by omega
        contradiction
      have h₁₃₄ : 1008 ≤ a * b := h₁₂ h₁₃₃
      linarith

  have h₁₄ : 108 ≤ Nat.lcm a b := by
    have h₁₄₁ : a * b = 6 * Nat.lcm a b := h₈
    have h₁₄₂ : 648 ≤ a * b := h₁₃
    have h₁₄₃ : 108 ≤ Nat.lcm a b := by
      omega
    exact h₁₄₃
  
  exact h₁₄