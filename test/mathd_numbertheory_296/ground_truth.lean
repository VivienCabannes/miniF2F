import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_296
  (n : ℕ)
  (h₀ : 2 ≤ n)
  (h₁ : ∃ x, x^3 = n)
  (h₂ : ∃ t, t^4 = n) :
  4096 ≤ n := by
  have h_main : n ≥ 4096 := by
    obtain ⟨t, ht⟩ := h₂
    have h₃ : t ≥ 2 := by
      by_contra h
      -- Assume t < 2, i.e., t = 0 or t = 1
      have h₄ : t ≤ 1 := by linarith
      have h₅ : t = 0 ∨ t = 1 := by
        have h₅₁ : t ≤ 1 := h₄
        have h₅₂ : t ≥ 0 := by positivity
        interval_cases t <;> simp_all (config := {decide := true})
      cases h₅ with
      | inl h₅ =>
        -- Case t = 0
        have h₆ : t = 0 := h₅
        rw [h₆] at ht
        norm_num at ht
        <;> linarith
      | inr h₅ =>
        -- Case t = 1
        have h₆ : t = 1 := h₅
        rw [h₆] at ht
        norm_num at ht
        <;> linarith
    -- We have t ≥ 2
    have h₄ : t ≥ 8 := by
      by_contra h
      -- Assume t < 8
      have h₅ : t ≤ 7 := by linarith
      have h₆ : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
        omega
      -- Check each case to see if t^4 is a perfect cube
      rcases h₆ with (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Case t = 2
        have h₇ : n = 16 := by
          norm_num at ht ⊢
          <;> linarith
        obtain ⟨x, hx⟩ := h₁
        have h₈ : x ^ 3 = 16 := by
          linarith
        have h₉ : x ≤ 2 := by
          by_contra h₉
          have h₁₀ : x ≥ 3 := by omega
          have h₁₁ : x ^ 3 ≥ 3 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left (by omega) 3
          linarith
        interval_cases x <;> norm_num at h₈ ⊢ <;> omega
      · -- Case t = 3
        have h₇ : n = 81 := by
          norm_num at ht ⊢
          <;> linarith
        obtain ⟨x, hx⟩ := h₁
        have h₈ : x ^ 3 = 81 := by
          linarith
        have h₉ : x ≤ 4 := by
          by_contra h₉
          have h₁₀ : x ≥ 5 := by omega
          have h₁₁ : x ^ 3 ≥ 5 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left (by omega) 3
          linarith
        interval_cases x <;> norm_num at h₈ ⊢ <;> omega
      · -- Case t = 4
        have h₇ : n = 256 := by
          norm_num at ht ⊢
          <;> linarith
        obtain ⟨x, hx⟩ := h₁
        have h₈ : x ^ 3 = 256 := by
          linarith
        have h₉ : x ≤ 6 := by
          by_contra h₉
          have h₁₀ : x ≥ 7 := by omega
          have h₁₁ : x ^ 3 ≥ 7 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left (by omega) 3
          linarith
        interval_cases x <;> norm_num at h₈ ⊢ <;> omega
      · -- Case t = 5
        have h₇ : n = 625 := by
          norm_num at ht ⊢
          <;> linarith
        obtain ⟨x, hx⟩ := h₁
        have h₈ : x ^ 3 = 625 := by
          linarith
        have h₉ : x ≤ 8 := by
          by_contra h₉
          have h₁₀ : x ≥ 9 := by omega
          have h₁₁ : x ^ 3 ≥ 9 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left (by omega) 3
          linarith
        interval_cases x <;> norm_num at h₈ ⊢ <;> omega
      · -- Case t = 6
        have h₇ : n = 1296 := by
          norm_num at ht ⊢
          <;> linarith
        obtain ⟨x, hx⟩ := h₁
        have h₈ : x ^ 3 = 1296 := by
          linarith
        have h₉ : x ≤ 10 := by
          by_contra h₉
          have h₁₀ : x ≥ 11 := by omega
          have h₁₁ : x ^ 3 ≥ 11 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left (by omega) 3
          linarith
        interval_cases x <;> norm_num at h₈ ⊢ <;> omega
      · -- Case t = 7
        have h₇ : n = 2401 := by
          norm_num at ht ⊢
          <;> linarith
        obtain ⟨x, hx⟩ := h₁
        have h₈ : x ^ 3 = 2401 := by
          linarith
        have h₉ : x ≤ 13 := by
          by_contra h₉
          have h₁₀ : x ≥ 14 := by omega
          have h₁₁ : x ^ 3 ≥ 14 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left (by omega) 3
          linarith
        interval_cases x <;> norm_num at h₈ ⊢ <;> omega
    -- Now we have t ≥ 8
    have h₅ : t ^ 4 ≥ 8 ^ 4 := by
      exact Nat.pow_le_pow_of_le_left h₄ 4
    have h₆ : n = t ^ 4 := by
      linarith
    have h₇ : n ≥ 4096 := by
      rw [h₆]
      <;> norm_num at h₅ ⊢ <;> linarith
    exact h₇
  -- We have n ≥ 4096
  linarith