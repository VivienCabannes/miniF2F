import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p1
  (S : Finset ℤ)
  (h₀ : ∀ (x : ℤ), x ∈ S ↔ ↑(abs x) < 3 * Real.pi):
  S.card = 19 := by
  have h_pi_lb : (9 : ℝ) < 3 * Real.pi := by
    have := Real.pi_gt_3141592
    norm_num at this ⊢
    <;> linarith
  
  have h_pi_ub : (3 : ℝ) * Real.pi < 10 := by
    have := Real.pi_lt_3141593
    norm_num at this ⊢
    <;> linarith
  
  have h_S_eq : S = Finset.Icc (-9 : ℤ) 9 := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_Icc, h₀]
    constructor
    · -- Prove the forward direction: if x ∈ S, then -9 ≤ x ≤ 9
      intro h
      have h₁ : (abs x : ℝ) < 3 * Real.pi := by exact_mod_cast h
      have h₂ : -9 ≤ (x : ℤ) := by
        by_contra h₂
        -- If x < -9, then x ≤ -10
        have h₃ : x ≤ -10 := by
          linarith
        have h₄ : (abs x : ℝ) ≥ 10 := by
          have h₅ : x ≤ -10 := h₃
          have h₆ : abs x ≥ 10 := by
            cases' abs_cases x with h₇ h₇ <;>
              (try omega) <;>
              (try
                {
                  norm_cast at h₇ ⊢ <;>
                    omega
                }) <;>
              (try
                {
                  simp_all [abs_of_nonneg, abs_of_nonpos, le_of_lt]
                  <;>
                  omega
                })
          have h₇ : (abs x : ℝ) ≥ 10 := by
            exact_mod_cast h₆
          exact h₇
        linarith
      have h₃ : (x : ℤ) ≤ 9 := by
        by_contra h₃
        -- If x > 9, then x ≥ 10
        have h₄ : x ≥ 10 := by
          linarith
        have h₅ : (abs x : ℝ) ≥ 10 := by
          have h₆ : x ≥ 10 := h₄
          have h₇ : abs x ≥ 10 := by
            cases' abs_cases x with h₈ h₈ <;>
              (try omega) <;>
              (try
                {
                  norm_cast at h₈ ⊢ <;>
                    omega
                }) <;>
              (try
                {
                  simp_all [abs_of_nonneg, abs_of_nonpos, le_of_lt]
                  <;>
                  omega
                })
          have h₈ : (abs x : ℝ) ≥ 10 := by
            exact_mod_cast h₇
          exact h₈
        linarith
      exact ⟨h₂, h₃⟩
    · -- Prove the reverse direction: if -9 ≤ x ≤ 9, then x ∈ S
      intro h
      have h₁ : -9 ≤ (x : ℤ) := h.1
      have h₂ : (x : ℤ) ≤ 9 := h.2
      have h₃ : (abs x : ℝ) < 3 * Real.pi := by
        have h₄ : abs x ≤ 9 := by
          have h₅ : -9 ≤ (x : ℤ) := h₁
          have h₆ : (x : ℤ) ≤ 9 := h₂
          have h₇ : abs x ≤ 9 := by
            cases' abs_cases x with h₈ h₈ <;>
              (try omega) <;>
              (try
                {
                  norm_cast at h₈ ⊢ <;>
                    omega
                }) <;>
              (try
                {
                  simp_all [abs_of_nonneg, abs_of_nonpos, le_of_lt]
                  <;>
                  omega
                })
          exact h₇
        have h₅ : (abs x : ℝ) ≤ 9 := by
          exact_mod_cast h₄
        have h₆ : (9 : ℝ) < 3 * Real.pi := h_pi_lb
        linarith
      exact_mod_cast h₃
  
  have h_finset_card : (Finset.Icc (-9 : ℤ) 9).card = 19 := by
    norm_num [Finset.Icc_self, Finset.card_empty]
    <;> rfl
  
  have h_main : S.card = 19 := by
    rw [h_S_eq]
    exact h_finset_card
  
  exact h_main