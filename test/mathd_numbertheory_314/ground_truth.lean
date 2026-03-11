import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_314
  (r n : ℕ)
  (h₀ : r = 1342 % 13)
  (h₁ : 0 < n)
  (h₂ : 1342∣n)
  (h₃ : n % 13 < r) :
  6710 ≤ n := by
  have h₄ : r = 3 := by
    norm_num [h₀, Nat.pow_succ, Nat.pow_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
    <;>
    rfl
  
  have h₅ : n % 13 < 3 := by
    rw [h₄] at h₃
    exact h₃
  
  have h₆ : ¬(n < 6710) := by
    intro h₆
    have h₇ : n < 6710 := h₆
    have h₈ : 1342 ∣ n := h₂
    have h₉ : n % 13 < 3 := h₅
    -- We need to show that if n < 6710 and 1342 ∣ n, then n % 13 ≥ 3, which contradicts h₉
    have h₁₀ : n = 1342 ∨ n = 2684 ∨ n = 4026 ∨ n = 5368 := by
      -- Since 1342 ∣ n and n < 6710, n must be one of these values
      have h₁₁ : n < 6710 := h₇
      have h₁₂ : 1342 ∣ n := h₂
      have h₁₃ : n > 0 := h₁
      -- Find all multiples of 1342 less than 6710
      have h₁₄ : n = 1342 ∨ n = 2684 ∨ n = 4026 ∨ n = 5368 := by
        -- Use the fact that n is a multiple of 1342 and n < 6710
        have h₁₅ : n < 6710 := h₇
        have h₁₆ : 1342 ∣ n := h₂
        obtain ⟨k, hk⟩ := h₁₆
        have h₁₇ : n = 1342 * k := by linarith
        have h₁₈ : k > 0 := by
          by_contra h
          have h₁₉ : k = 0 := by omega
          rw [h₁₉] at h₁₇
          omega
        have h₂₀ : k < 5 := by
          by_contra h
          have h₂₁ : k ≥ 5 := by omega
          have h₂₂ : n ≥ 1342 * 5 := by
            nlinarith
          omega
        interval_cases k <;> norm_num [h₁₇] at h₁₅ ⊢ <;> omega
      exact h₁₄
    -- Check each case to see if n % 13 < 3
    rcases h₁₀ with (rfl | rfl | rfl | rfl)
    · -- Case n = 1342
      norm_num at h₉ ⊢ <;> omega
    · -- Case n = 2684
      norm_num at h₉ ⊢ <;> omega
    · -- Case n = 4026
      norm_num at h₉ ⊢ <;> omega
    · -- Case n = 5368
      norm_num at h₉ ⊢ <;> omega
  
  have h₇ : 6710 ≤ n := by
    by_contra h₈
    -- If n is not at least 6710, then n < 6710
    have h₉ : n < 6710 := by omega
    -- This contradicts h₆, which states that n cannot be less than 6710
    exact h₆ h₉
  
  exact h₇