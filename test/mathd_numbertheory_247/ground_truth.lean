import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_247
  (n : ℕ)
  (h₀ : (3 * n) % 11 = 2) :
  n % 11 = 8 := by
  have h₁ : n % 11 = 8 := by
    have h₂ : 3 * (n % 11) % 11 = 2 := by
      have h₃ : 3 * n % 11 = 2 := h₀
      have h₄ : 3 * (n % 11) % 11 = 3 * n % 11 := by
        have h₅ : 3 * (n % 11) % 11 = (3 * n) % 11 := by
          have h₆ : 3 * (n % 11) = (3 * n) % 33 := by
            omega
          have h₇ : (3 * n) % 33 % 11 = (3 * n) % 11 := by
            omega
          omega
        omega
      rw [h₄, h₃]
    -- Check all possible values of n % 11 to find that only n % 11 = 8 satisfies 3 * (n % 11) % 11 = 2
    have h₈ : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
      omega
    rcases h₈ with (h₈ | h₈ | h₈ | h₈ | h₈ | h₈ | h₈ | h₈ | h₈ | h₈ | h₈) <;>
      (try omega) <;>
      (try
        {
          simp [h₈, h₈, h₈, h₈, h₈, h₈, h₈, h₈, h₈, h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at h₂ ⊢
          <;> omega
        }) <;>
      (try
        {
          simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at h₂ ⊢ <;> omega
        })
  exact h₁