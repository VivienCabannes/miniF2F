import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_x5neqy2p4
  (x y : ℤ) :
  x^5 ≠ y^2 + 4 := by
  have h_main : (x ^ 5 - (y ^ 2 + 4)) % 11 ≠ 0 := by
    have h₁ : (x ^ 5 : ℤ) % 11 = 0 ∨ (x ^ 5 : ℤ) % 11 = 1 ∨ (x ^ 5 : ℤ) % 11 = 10 := by
      have h₂ : (x : ℤ) % 11 = 0 ∨ (x : ℤ) % 11 = 1 ∨ (x : ℤ) % 11 = 2 ∨ (x : ℤ) % 11 = 3 ∨ (x : ℤ) % 11 = 4 ∨ (x : ℤ) % 11 = 5 ∨ (x : ℤ) % 11 = 6 ∨ (x : ℤ) % 11 = 7 ∨ (x : ℤ) % 11 = 8 ∨ (x : ℤ) % 11 = 9 ∨ (x : ℤ) % 11 = 10 := by
        omega
      rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂) <;>
        (try omega) <;>
        (try
          {
            simp [h₂, pow_succ, Int.mul_emod, Int.sub_emod, Int.add_emod]
          }) <;>
        (try norm_num) <;>
        (try omega) <;>
        (try
          {
            (try norm_num) <;>
            (try omega)
          })
    have h₃ : (y ^ 2 + 4 : ℤ) % 11 = 2 ∨ (y ^ 2 + 4 : ℤ) % 11 = 4 ∨ (y ^ 2 + 4 : ℤ) % 11 = 5 ∨ (y ^ 2 + 4 : ℤ) % 11 = 7 ∨ (y ^ 2 + 4 : ℤ) % 11 = 8 ∨ (y ^ 2 + 4 : ℤ) % 11 = 9 := by
      have h₄ : (y : ℤ) % 11 = 0 ∨ (y : ℤ) % 11 = 1 ∨ (y : ℤ) % 11 = 2 ∨ (y : ℤ) % 11 = 3 ∨ (y : ℤ) % 11 = 4 ∨ (y : ℤ) % 11 = 5 ∨ (y : ℤ) % 11 = 6 ∨ (y : ℤ) % 11 = 7 ∨ (y : ℤ) % 11 = 8 ∨ (y : ℤ) % 11 = 9 ∨ (y : ℤ) % 11 = 10 := by
        omega
      rcases h₄ with (h₄ | h₄ | h₄ | h₄ | h₄ | h₄ | h₄ | h₄ | h₄ | h₄ | h₄) <;>
        (try omega) <;>
        (try
          {
            simp [h₄, pow_two, Int.mul_emod, Int.add_emod, Int.emod_emod]
          }) <;>
        (try norm_num) <;>
        (try omega) <;>
        (try
          {
            (try norm_num) <;>
            (try omega)
          })
    rcases h₁ with (h₁ | h₁ | h₁) <;>
      rcases h₃ with (h₃ | h₃ | h₃ | h₃ | h₃ | h₃) <;>
        (try omega) <;>
        (try
          {
            norm_num [Int.sub_emod, h₁, h₃, Int.emod_emod] at *
            <;> omega
          })
  
  have h_final : x ^ 5 ≠ y ^ 2 + 4 := by
    intro h_contra
    have h₁ : (x ^ 5 - (y ^ 2 + 4) : ℤ) % 11 = 0 := by
      rw [h_contra]
      <;> simp [Int.emod_self]
    have h₂ : (x ^ 5 - (y ^ 2 + 4) : ℤ) % 11 ≠ 0 := h_main
    contradiction
  
  exact h_final