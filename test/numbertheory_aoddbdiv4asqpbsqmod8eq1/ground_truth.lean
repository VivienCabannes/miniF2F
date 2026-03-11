import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1
  (a : ℤ)
  (b : ℤ)
  (h₀ : Odd a)
  (h₁ : 4 ∣ b)
  (h₂ : b >= 0) :
  (a^2 + b^2) % 8 = 1 := by
  have h₂ : (a ^ 2 : ℤ) % 8 = 1 := by
    have h₂₁ : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
      cases' h₀ with k hk
      have : a % 8 = (2 * k + 1) % 8 := by omega
      have h₂₂ : (2 * k + 1 : ℤ) % 8 = 1 ∨ (2 * k + 1 : ℤ) % 8 = 3 ∨ (2 * k + 1 : ℤ) % 8 = 5 ∨ (2 * k + 1 : ℤ) % 8 = 7 := by
        have : (k : ℤ) % 8 = 0 ∨ (k : ℤ) % 8 = 1 ∨ (k : ℤ) % 8 = 2 ∨ (k : ℤ) % 8 = 3 ∨ (k : ℤ) % 8 = 4 ∨ (k : ℤ) % 8 = 5 ∨ (k : ℤ) % 8 = 6 ∨ (k : ℤ) % 8 = 7 := by
          omega
        rcases this with (h | h | h | h | h | h | h | h) <;>
          (try omega) <;>
          (try { simp [h, Int.add_emod, Int.mul_emod, pow_two] <;> omega }) <;>
          (try { omega }) <;>
          (try { ring_nf at * <;> omega })
      rcases h₂₂ with (h₂₂ | h₂₂ | h₂₂ | h₂₂) <;> omega
    rcases h₂₁ with (h₂₁ | h₂₁ | h₂₁ | h₂₁) <;>
      (try simp [h₂₁, pow_two, Int.mul_emod, Int.add_emod]) <;>
      (try norm_num) <;>
      (try ring_nf at * <;> omega)
  
  have h₃ : ((b ^ 2 : ℕ) : ℤ) % 8 = 0 := by
    have h₃₁ : (4 : ℕ) ∣ b := h₁
    have h₃₂ : (8 : ℕ) ∣ b ^ 2 := by
      have h₃₃ : (4 : ℕ) ∣ b := h₁
      have h₃₄ : (8 : ℕ) ∣ b ^ 2 := by
        obtain ⟨k, hk⟩ := h₃₃
        have h₃₅ : b = 4 * k := by omega
        rw [h₃₅]
        have h₃₆ : (8 : ℕ) ∣ (4 * k : ℕ) ^ 2 := by
          ring_nf at *
          use 2 * k ^ 2
          <;> ring_nf at * <;> omega
        exact h₃₆
      exact h₃₄
    have h₃₃ : ((b ^ 2 : ℕ) : ℤ) % 8 = 0 := by
      have h₃₄ : (8 : ℕ) ∣ b ^ 2 := h₃₂
      have h₃₅ : ((b ^ 2 : ℕ) : ℤ) % 8 = 0 := by
        have h₃₆ : (b ^ 2 : ℕ) % 8 = 0 := by
          omega
        have h₃₇ : ((b ^ 2 : ℕ) : ℤ) % 8 = 0 := by
          norm_cast at h₃₆ ⊢
          <;> omega
        exact h₃₇
      exact h₃₅
    exact h₃₃
  
  have h₄ : (a ^ 2 + (b ^ 2 : ℤ)) % 8 = 1 := by
    have h₄₁ : (a ^ 2 + (b ^ 2 : ℤ)) % 8 = ((a ^ 2 : ℤ) % 8 + ((b ^ 2 : ℕ) : ℤ) % 8) % 8 := by
      simp [Int.add_emod, Int.emod_emod]
      <;> norm_cast
      <;> ring_nf at *
      <;> omega
    rw [h₄₁]
    rw [h₂, h₃]
    <;> norm_num
    <;> ring_nf at *
    <;> omega
  
  have h₅ : (a ^ 2 + b ^ 2) % 8 = 1 := by
    -- Cast b^2 to integer and use the previous results to conclude the proof.
    have h₅₁ : (a ^ 2 + b ^ 2 : ℤ) = (a ^ 2 + (b ^ 2 : ℤ)) := by
      norm_cast
    rw [h₅₁]
    exact h₄
  
  exact h₅