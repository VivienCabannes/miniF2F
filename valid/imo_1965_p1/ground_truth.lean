import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1965_p1 (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 2 * π)
  (h₂ : 2 * Real.cos x ≤ abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))))
  (h₃ : abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))) ≤ Real.sqrt 2) :
  π / 4 ≤ x ∧ x ≤ 7 * π / 4 := by
  have h₄ : abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))) ^ 2 = 2 - 2 * abs (Real.cos (2 * x)) := by
    have h₄ : 0 ≤ Real.sqrt (1 + Real.sin (2 * x)) := Real.sqrt_nonneg _
    have h₅ : 0 ≤ Real.sqrt (1 - Real.sin (2 * x)) := Real.sqrt_nonneg _
    have h₆ : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have h₇ : 0 ≤ Real.sqrt (1 + Real.sin (2 * x)) * Real.sqrt (1 - Real.sin (2 * x)) := mul_nonneg h₄ h₅
    cases' le_total 0 (Real.cos (2 * x)) with h₈ h₈ <;>
      cases' le_total 0 (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))) with h₉ h₉ <;>
        simp_all [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
          nlinarith [Real.sq_sqrt (show 0 ≤ 1 + Real.sin (2 * x) by nlinarith [Real.sin_le_one (2 * x), Real.neg_one_le_sin (2 * x)]),
            Real.sq_sqrt (show 0 ≤ 1 - Real.sin (2 * x) by nlinarith [Real.sin_le_one (2 * x), Real.neg_one_le_sin (2 * x)]),
            Real.sq_sqrt (show 0 ≤ 2 by norm_num),
            Real.cos_sq_add_sin_sq (2 * x)]
  have h₅ : 2 * Real.cos x ≤ Real.sqrt (2 - 2 * abs (Real.cos (2 * x))) := by
    nlinarith [abs_nonneg (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))),
      Real.sq_sqrt (show 0 ≤ 2 - 2 * abs (Real.cos (2 * x)) by linarith [abs_cos_le_one (2 * x)]),
      Real.sqrt_nonneg (2 - 2 * abs (Real.cos (2 * x))),
      sq_nonneg (Real.cos x - Real.sqrt (2 - 2 * abs (Real.cos (2 * x)))),
      sq_nonneg (Real.cos x + Real.sqrt (2 - 2 * abs (Real.cos (2 * x)))),
      Real.sqrt_nonneg (2 - 2 * abs (Real.cos (2 * x))),
      Real.sq_sqrt (show 0 ≤ 2 - 2 * abs (Real.cos (2 * x)) by linarith [abs_cos_le_one (2 * x)])]
  
  have h₆ : Real.cos x ≤ Real.sqrt 2 / 2 := by
    have h₆ : Real.cos x ≤ Real.sqrt 2 / 2 := by
      apply le_of_sub_nonneg
      have h₇ : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have h₈ : 0 ≤ Real.sqrt (2 - 2 * abs (Real.cos (2 * x))) := Real.sqrt_nonneg _
      have h₉ : Real.cos x ≤ Real.sqrt (2 - 2 * abs (Real.cos (2 * x))) / 2 := by
        nlinarith [sq_sqrt (show 0 ≤ 2 by norm_num), sq_sqrt (show 0 ≤ 2 - 2 * abs (Real.cos (2 * x)) by nlinarith [abs_cos_le_one (2 * x)]),
          h₅, sq_nonneg (Real.cos x - Real.sqrt 2 / 2)]
      nlinarith [sq_sqrt (show 0 ≤ 2 by norm_num), sq_sqrt (show 0 ≤ 2 - 2 * abs (Real.cos (2 * x)) by nlinarith [abs_cos_le_one (2 * x)]),
        h₅, sq_nonneg (Real.cos x - Real.sqrt 2 / 2)]
    exact h₆
  
  have h₇ : Real.pi / 4 ≤ x ∧ x ≤ 7 * Real.pi / 4 := by
    have h₇ : Real.pi / 4 ≤ x := by
      contrapose! h₆
      have h₇₀ : x < Real.pi / 4 := by linarith
      have h₇₁ : Real.cos x > Real.sqrt 2 / 2 := by
        rw [← Real.cos_pi_div_four]
        apply Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith)
        <;> linarith
      linarith
    have h₈ : x ≤ 7 * Real.pi / 4 := by
      contrapose! h₆
      have h₈₀ : x > 7 * Real.pi / 4 := by linarith
      have h₈₁ : Real.cos x > Real.sqrt 2 / 2 := by
        have h₈₂ : Real.cos x = Real.cos (2 * Real.pi - x) := by
          rw [Real.cos_two_pi_sub]
        rw [h₈₂]
        have h₈₃ : 2 * Real.pi - x < 7 * Real.pi / 4 := by linarith
        have h₈₄ : Real.cos (2 * Real.pi - x) > Real.sqrt 2 / 2 := by
          rw [← Real.cos_pi_div_four]
          apply Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith)
          <;> linarith
        linarith
      linarith
    exact ⟨h₇, h₈⟩
  
  -- We have already established the bounds for x in the given hypotheses.
  -- We need to show that x is within the interval [π/4, 7π/4].
  have h₈ : Real.pi / 4 ≤ x := by
    linarith [h₇.1]
  have h₉ : x ≤ 7 * Real.pi / 4 := by
    linarith [h₇.2]
  -- Combining the lower and upper bounds, we conclude that x is within the interval [π/4, 7π/4].
  exact ⟨h₈, h₉⟩