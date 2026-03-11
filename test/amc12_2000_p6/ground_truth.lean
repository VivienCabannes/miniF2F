import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p6
  (p q : ℕ)
  (h₀ : Nat.Prime p ∧ Nat.Prime q)
  (h₁ : 4 ≤ p ∧ p ≤ 18)
  (h₂ : 4 ≤ q ∧ q ≤ 18) :
  p * q - (p + q) ≠ 194 := by
  have h₃ : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
    have h₃₁ : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
      have h₄ := h₀.1
      have h₅ : p ≤ 18 := by linarith
      have h₆ : 4 ≤ p := by linarith
      interval_cases p <;> norm_num [Nat.Prime] at h₄ ⊢ <;> aesop
    exact h₃₁
    <;> aesop
  
  have h₄ : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
    have h₄₁ : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
      have h₅ := h₀.2
      have h₆ : q ≤ 18 := by linarith
      have h₇ : 4 ≤ q := by linarith
      interval_cases q <;> norm_num [Nat.Prime] at h₅ ⊢ <;> aesop
    exact h₄₁
    <;> aesop
  
  have h₅ : p * q ≥ p + q := by
    have h₅₁ : p ≥ 5 := by
      have h₅₂ := h₀.1.two_le
      have h₅₃ := h₁.1
      have h₅₄ : p ≥ 4 := by linarith
      have h₅₅ : p ≠ 4 := by
        intro h
        rw [h] at h₀
        norm_num [Nat.Prime] at h₀
      omega
    have h₅₂ : q ≥ 5 := by
      have h₅₃ := h₀.2.two_le
      have h₅₄ := h₂.1
      have h₅₅ : q ≥ 4 := by linarith
      have h₅₆ : q ≠ 4 := by
        intro h
        rw [h] at h₀
        norm_num [Nat.Prime] at h₀
      omega
    have h₅₃ : p * q ≥ p + q := by
      nlinarith [mul_le_mul_of_nonneg_right h₅₁ (by linarith : (0 : ℕ) ≤ q),
        mul_le_mul_of_nonneg_left h₅₂ (by linarith : (0 : ℕ) ≤ p)]
    exact h₅₃
  
  have h₆ : p * q - (p + q) ≠ 194 := by
    have h₆₁ : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := h₃
    have h₆₂ : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := h₄
    rcases h₆₁ with (rfl | rfl | rfl | rfl | rfl) <;> rcases h₆₂ with (rfl | rfl | rfl | rfl | rfl) <;> norm_num at h₅ ⊢ <;>
      (try omega) <;> (try ring_nf at h₅ ⊢ <;> omega)
    <;>
      (try omega)
    <;>
      (try ring_nf at h₅ ⊢ <;> omega)
  
  intro h₇
  have h₈ : p * q - (p + q) ≠ 194 := h₆
  have h₉ : ↑p * ↑q - (↑p + ↑q) = (194 : ℕ) := by simpa [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc] using h₇
  have h₁₀ : p * q - (p + q) = 194 := by simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_sub, h₅] using h₉
  exact h₈ h₁₀