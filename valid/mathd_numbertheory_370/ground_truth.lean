import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_370 (n : ℕ) (h₀ : n % 7 = 3) : (2 * n + 1) % 7 = 0 := by
  have h₁ : ∃ k : ℕ, n = 7 * k + 3 := by
    use n / 7
    have h₁ : n = 7 * (n / 7) + (n % 7) := by
      rw [Nat.div_add_mod]
    rw [h₀] at h₁
    linarith
  
  have h₂ : ∀ k : ℕ, 2 * (7 * k + 3) + 1 = 14 * k + 7 := by
    intro k
    -- Simplify the expression using basic arithmetic operations and properties
    simp [h₁, mul_add, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
    -- Use the omega tactic to solve the linear arithmetic problem
    <;> omega
  
  have h₃ : ∀ k : ℕ, 14 * k + 7 = 7 * (2 * k + 1) := by
    intro k
    -- Simplify the expression 14 * k + 7 to show it is a multiple of 7.
    have h₃ := h₂ k
    -- Use the fact that 14 * k + 7 = 7 * (2 * k + 1) to conclude the proof.
    linarith
  
  have h₄ : (2 * n + 1) % 7 = 0 := by
    obtain ⟨k, hk⟩ := h₁
    rw [hk]
    simp [h₂, h₃, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  
  have h₅ := h₂ 0
  have h₆ := h₃ 0
  simp at h₅ h₆
  have h₇ := h₂ 1
  have h₈ := h₃ 1
  simp at h₇ h₈
  have h₉ := h₂ 2
  have h₁₀ := h₃ 2
  simp at h₉ h₁₀
  have h₁₁ := h₂ 3
  have h₁₂ := h₃ 3
  simp at h₁₁ h₁₂
  omega