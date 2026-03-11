import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1960_p2
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9)
  (h₃ : x ≠ 0) :
  -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h₃ : -(1 / 2 : ℝ) ≤ x := by
    have h₃₁ : 0 ≤ 1 + 2 * x := h₀
    have h₃₂ : -(1 / 2 : ℝ) ≤ x := by linarith
    exact h₃₂
  
  have h₄ : x < 45 / 8 := by
    by_cases hx : x > 0
    · -- Case: x > 0
      have h₅ : Real.sqrt (1 + 2 * x) > 1 := by
        apply Real.lt_sqrt_of_sq_lt
        nlinarith
      have h₆ : Real.sqrt (1 + 2 * x) ≠ 1 := by
        intro h
        have h₇ : Real.sqrt (1 + 2 * x) = 1 := h
        have h₈ : (Real.sqrt (1 + 2 * x)) ^ 2 = (1 : ℝ) ^ 2 := by rw [h₇]
        have h₉ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
          rw [Real.sq_sqrt] <;> nlinarith
        have h₁₀ : 1 + 2 * x = 1 := by nlinarith
        have h₁₁ : x = 0 := by nlinarith
        have h₁₂ : x > 0 := hx
        linarith
      have h₇ : Real.sqrt (1 + 2 * x) < 7 / 2 := by
        by_contra h₇
        have h₈ : Real.sqrt (1 + 2 * x) ≥ 7 / 2 := by linarith
        have h₉ : (Real.sqrt (1 + 2 * x) - 1) ^ 2 ≥ (7 / 2 - 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x)]
        have h₁₀ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≥ 2 * x + 9 := by
          have h₁₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 := by
            ring_nf
            <;>
            nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x)]
          rw [h₁₁]
          have h₁₂ : x = ((Real.sqrt (1 + 2 * x)) ^ 2 - 1) / 2 := by
            nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x), Real.sqrt_nonneg (1 + 2 * x)]
          rw [h₁₂]
          have h₁₃ : 0 < Real.sqrt (1 + 2 * x) - 1 := by nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x)]
          have h₁₄ : 0 < (Real.sqrt (1 + 2 * x) - 1) ^ 2 := by nlinarith
          field_simp [h₁₄.ne']
          rw [le_div_iff (by positivity)]
          nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x), Real.sqrt_nonneg (1 + 2 * x),
            sq_nonneg (Real.sqrt (1 + 2 * x) - 7 / 2)]
        linarith
      have h₈ : x < 45 / 8 := by
        nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ 1 + 2 * x), Real.sqrt_nonneg (1 + 2 * x)]
      exact h₈
    · -- Case: x ≤ 0
      have h₅ : x < 45 / 8 := by
        by_cases h₅₁ : x < 0
        · -- Subcase: x < 0
          linarith
        · -- Subcase: x = 0
          have h₅₂ : x = 0 := by
            by_contra h₅₂
            have h₅₃ : x > 0 := by
              by_contra h₅₄
              have h₅₅ : x < 0 := by
                cases' lt_or_gt_of_ne h₅₂ with h₅₅ h₅₅
                · linarith
                · exfalso
                  linarith
              linarith
            linarith
          exfalso
          have h₅₃ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
            rw [h₅₂]
            have h₅₄ : Real.sqrt (1 + 2 * (0 : ℝ)) = 1 := by norm_num [Real.sqrt_eq_iff_sq_eq]
            rw [h₅₄]
            <;> norm_num
          exact h₁ h₅₃
      exact h₅
  
  exact ⟨h₃, h₄⟩