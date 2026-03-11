import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_5
  (n : ℕ)
  (h₀ : 10 ≤ n)
  (h₁ : ∃ x, x^2 = n)
  (h₂ : ∃ t, t^3 = n) :
  64 ≤ n := by
  have h₃ : ∀ (t : ℕ), t ^ 3 = n → 64 ≤ n := by
    intro t ht
    have h₄ : t ≥ 3 := by
      by_contra h
      -- If t < 3, then t ≤ 2
      have h₅ : t ≤ 2 := by linarith
      have h₆ : t ^ 3 ≤ 8 := by
        have h₇ : t ≤ 2 := h₅
        have h₈ : t ^ 3 ≤ 2 ^ 3 := by
          exact Nat.pow_le_pow_of_le_left h₇ 3
        linarith
      have h₉ : n ≤ 8 := by linarith
      linarith
    -- Now we have t ≥ 3
    by_cases h₅ : t ≥ 4
    · -- If t ≥ 4, then t³ ≥ 64
      have h₆ : t ^ 3 ≥ 4 ^ 3 := by
        exact Nat.pow_le_pow_of_le_left h₅ 3
      have h₇ : n ≥ 64 := by
        linarith
      linarith
    · -- If t < 4 and t ≥ 3, then t = 3
      have h₆ : t = 3 := by
        have h₇ : t < 4 := by linarith
        have h₈ : t ≥ 3 := h₄
        interval_cases t <;> norm_num at h₇ h₈ ⊢ <;> try omega
      rw [h₆] at ht
      -- If t = 3, then n = 27
      have h₇ : n = 27 := by
        norm_num at ht ⊢
        <;> linarith
      -- But 27 is not a perfect square
      rcases h₁ with ⟨x, hx⟩
      have h₈ : x ^ 2 = 27 := by
        norm_num [h₇] at hx ⊢
        <;> linarith
      have h₉ : x ≤ 5 := by
        nlinarith
      have h₁₀ : x ≥ 6 := by
        by_contra h
        have h₁₁ : x ≤ 5 := by linarith
        interval_cases x <;> norm_num at h₈ ⊢ <;> try omega
      linarith
  
  have h₄ : 64 ≤ n := by
    rcases h₂ with ⟨t, ht⟩
    have h₅ : 64 ≤ n := h₃ t ht
    exact h₅
  
  exact h₄