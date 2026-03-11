import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_170
  (S : Finset ℤ)
  (h₀ : ∀ (n : ℤ), n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
  S.card = 11 := by
  have h₁ : S = Finset.Icc (-3) 7 := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_Icc, h₀]
    constructor
    · intro h
      have h₂ : abs (n - 2) ≤ 5 := by
        norm_num at h ⊢
        <;>
        (try omega) <;>
        (try
          {
            cases' le_or_lt 0 (n - 2) with h₃ h₃ <;>
            simp_all [abs_of_nonneg, abs_of_neg, le_of_lt] <;>
            omega
          })
        <;>
        omega
      have h₃ : -3 ≤ n := by
        have h₄ : abs (n - 2) ≤ 5 := h₂
        cases' le_or_lt 0 (n - 2) with h₅ h₅
        · -- Case: n - 2 ≥ 0
          have h₆ : n - 2 ≤ 5 := by
            rw [abs_of_nonneg h₅] at h₄
            linarith
          omega
        · -- Case: n - 2 < 0
          have h₆ : -(n - 2) ≤ 5 := by
            rw [abs_of_neg h₅] at h₄
            linarith
          omega
      have h₄ : n ≤ 7 := by
        have h₅ : abs (n - 2) ≤ 5 := h₂
        cases' le_or_lt 0 (n - 2) with h₆ h₆
        · -- Case: n - 2 ≥ 0
          have h₇ : n - 2 ≤ 5 := by
            rw [abs_of_nonneg h₆] at h₅
            linarith
          omega
        · -- Case: n - 2 < 0
          have h₇ : -(n - 2) ≤ 5 := by
            rw [abs_of_neg h₆] at h₅
            linarith
          omega
      exact ⟨h₃, h₄⟩
    · intro h
      have h₂ : -3 ≤ n := h.1
      have h₃ : n ≤ 7 := h.2
      have h₄ : abs (n - 2) ≤ 5 := by
        have h₅ : -3 ≤ n := h₂
        have h₆ : n ≤ 7 := h₃
        cases' le_or_lt 0 (n - 2) with h₇ h₇
        · -- Case: n - 2 ≥ 0
          have h₈ : n - 2 ≤ 5 := by
            omega
          rw [abs_of_nonneg h₇]
          linarith
        · -- Case: n - 2 < 0
          have h₈ : -(n - 2) ≤ 5 := by
            omega
          rw [abs_of_neg h₇]
          linarith
      norm_num at h₄ ⊢
      <;>
      (try omega) <;>
      (try
        {
          cases' le_or_lt 0 (n - 2) with h₅ h₅ <;>
          simp_all [abs_of_nonneg, abs_of_neg, le_of_lt] <;>
          omega
        })
      <;>
      omega
  
  have h₂ : S.card = 11 := by
    rw [h₁]
    -- We need to compute the cardinality of the interval [-3, 7]
    -- This can be done by directly evaluating the cardinality of the finset
    rfl
  
  apply h₂