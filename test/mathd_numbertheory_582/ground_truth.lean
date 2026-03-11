import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_582
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 3∣n) :
  ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 := by
  have h₂ : (n + 4 + (n + 6) + (n + 8)) = 3 * n + 18 := by
    have h₂₁ : n + 4 + (n + 6) + (n + 8) = 3 * n + 18 := by
      have h₂₂ : n + 4 + (n + 6) + (n + 8) = (n + 4 + (n + 6)) + (n + 8) := by
        ring
      rw [h₂₂]
      have h₂₃ : n + 4 + (n + 6) = 2 * n + 10 := by
        ring
      rw [h₂₃]
      have h₂₄ : (2 * n + 10) + (n + 8) = 3 * n + 18 := by
        ring
      rw [h₂₄]
      <;> ring
    rw [h₂₁]
    <;> ring
  
  have h₃ : (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
    rw [h₂]
    have h₄ : 3 ∣ n := h₁
    have h₅ : n % 9 = 0 ∨ n % 9 = 3 ∨ n % 9 = 6 := by
      -- Prove that n % 9 can only be 0, 3, or 6 when 3 divides n
      have h₅₁ : n % 9 = 0 ∨ n % 9 = 3 ∨ n % 9 = 6 := by
        omega
      exact h₅₁
    rcases h₅ with (h₅ | h₅ | h₅)
    · -- Case n % 9 = 0
      simp [h₅, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_self, Nat.zero_add,
        Nat.add_assoc]
      <;> norm_num <;> omega
    · -- Case n % 9 = 3
      simp [h₅, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_self, Nat.zero_add,
        Nat.add_assoc]
      <;> norm_num <;> omega
    · -- Case n % 9 = 6
      simp [h₅, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_self, Nat.zero_add,
        Nat.add_assoc]
      <;> norm_num <;> omega
  
  exact h₃