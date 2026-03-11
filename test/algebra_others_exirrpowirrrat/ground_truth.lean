import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  have h_main : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
    by_cases h : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
    · -- Case 1: (√2)^(√2) is irrational
      have h₁ : Irrational (Real.sqrt 2 ^ Real.sqrt 2) := h
      have h₂ : Irrational (Real.sqrt 2) := by
        exact irrational_sqrt_two
      -- Take a = (√2)^(√2) and b = √2
      have h₃ : (Real.sqrt 2 ^ Real.sqrt 2 : ℝ) > 0 := by positivity
      have h₄ : ((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2 = 2 := by
        have h₅ : Real.log (((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2) = Real.log 2 := by
          have h₅₁ : Real.log (((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2) = Real.sqrt 2 * Real.log (Real.sqrt 2 ^ Real.sqrt 2 : ℝ) := by
            rw [Real.log_rpow (by positivity)]
            <;>
            norm_num
          rw [h₅₁]
          have h₅₂ : Real.log (Real.sqrt 2 ^ Real.sqrt 2 : ℝ) = Real.sqrt 2 * Real.log (Real.sqrt 2) := by
            rw [Real.log_rpow (by positivity)]
            <;>
            norm_num
          rw [h₅₂]
          have h₅₃ : Real.sqrt 2 * (Real.sqrt 2 * Real.log (Real.sqrt 2)) = 2 * Real.log (Real.sqrt 2) := by
            ring_nf
            <;>
            field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num
          rw [h₅₃]
          have h₅₄ : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
            have h₅₄₁ : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
              have h₅₄₂ : Real.sqrt 2 > 0 := by positivity
              have h₅₄₃ : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
                rw [Real.log_sqrt (by positivity)]
                <;> ring
              exact h₅₄₃
            exact h₅₄₁
          rw [h₅₄]
          have h₅₅ : (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 := by ring
          rw [h₅₅]
        -- Use the fact that the logarithm is injective to conclude the proof
        have h₅₆ : Real.log (((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2) = Real.log 2 := h₅
        have h₅₇ : ((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2 > 0 := by positivity
        have h₅₈ : Real.log (((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2) = Real.log 2 := h₅
        have h₅₉ : ((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2 = 2 := by
          apply Real.log_injOn_pos (Set.mem_Ioi.mpr h₅₇) (Set.mem_Ioi.mpr (by positivity))
          rw [h₅₈]
          <;>
          norm_num
        exact h₅₉
      have h₅ : ¬Irrational (((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2) := by
        intro h₅₁
        have h₅₂ : Irrational (((Real.sqrt 2 ^ Real.sqrt 2 : ℝ) : ℝ) ^ Real.sqrt 2) := h₅₁
        have h₅₃ : (Irrational (2 : ℝ)) := by simpa [h₄] using h₅₂
        exact h₅₃ ⟨2, by norm_num⟩
      refine' ⟨(Real.sqrt 2 ^ Real.sqrt 2 : ℝ), Real.sqrt 2, h₁, h₂, _⟩
      simpa using h₅
    · -- Case 2: (√2)^(√2) is rational
      have h₁ : ¬Irrational (Real.sqrt 2 ^ Real.sqrt 2) := h
      have h₂ : Irrational (Real.sqrt 2) := by
        exact irrational_sqrt_two
      -- Take a = √2 and b = √2
      refine' ⟨Real.sqrt 2, Real.sqrt 2, h₂, h₂, _⟩
      have h₃ : ¬Irrational (Real.sqrt 2 ^ Real.sqrt 2) := h₁
      simpa using h₃
  simpa using h_main