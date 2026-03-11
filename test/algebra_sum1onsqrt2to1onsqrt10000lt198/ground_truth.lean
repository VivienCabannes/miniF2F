import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∑ k ∈ (Finset.Icc (2 : ℕ) 10000), (1 / Real.sqrt k) < 198 := by
  have h₁ : ∀ (k : ℕ), k ∈ Finset.Icc (2 : ℕ) 10000 → (1 : ℝ) / Real.sqrt k < 2 * (Real.sqrt k - Real.sqrt (k - 1)) := by
    intro k hk
    have h₂ : 2 ≤ k ∧ k ≤ 10000 := by simpa using Finset.mem_Icc.mp hk
    have h₃ : (k : ℝ) ≥ 2 := by exact_mod_cast h₂.1
    have h₄ : (k : ℝ) ≤ 10000 := by exact_mod_cast h₂.2
    have h₅ : (k : ℝ) - 1 ≥ 1 := by
      have h₅₁ : (k : ℝ) ≥ 2 := h₃
      linarith
    have h₆ : Real.sqrt (k : ℝ) ≥ 0 := Real.sqrt_nonneg _
    have h₇ : Real.sqrt ((k : ℝ) - 1) ≥ 0 := Real.sqrt_nonneg _
    have h₈ : Real.sqrt (k : ℝ) > 0 := Real.sqrt_pos.mpr (by linarith)
    have h₉ : Real.sqrt ((k : ℝ) - 1) > 0 := Real.sqrt_pos.mpr (by linarith)
    -- Prove that 1 / Real.sqrt k < 2 * (Real.sqrt k - Real.sqrt (k - 1))
    have h₁₀ : (1 : ℝ) / Real.sqrt k < 2 * (Real.sqrt k - Real.sqrt (k - 1)) := by
      have h₁₀₁ : Real.sqrt k > Real.sqrt ((k : ℝ) - 1) := by
        apply Real.sqrt_lt_sqrt
        <;> nlinarith
      have h₁₀₂ : Real.sqrt k - Real.sqrt ((k : ℝ) - 1) > 0 := by linarith
      have h₁₀₃ : 2 * (Real.sqrt k - Real.sqrt ((k : ℝ) - 1)) > 0 := by positivity
      -- Use the identity involving square roots to prove the inequality
      have h₁₀₄ : (Real.sqrt k - Real.sqrt ((k : ℝ) - 1)) * (Real.sqrt k + Real.sqrt ((k : ℝ) - 1)) = 1 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) by linarith),
          Real.sq_sqrt (show 0 ≤ (k : ℝ) - 1 by linarith),
          mul_nonneg h₆ h₇, h₈.le, h₉.le]
      have h₁₀₅ : (Real.sqrt k + Real.sqrt ((k : ℝ) - 1)) > 0 := by positivity
      have h₁₀₆ : 2 * (Real.sqrt k - Real.sqrt ((k : ℝ) - 1)) > 1 / Real.sqrt k := by
        have h₁₀₇ : (1 : ℝ) / Real.sqrt k < 2 * (Real.sqrt k - Real.sqrt ((k : ℝ) - 1)) := by
          -- Use the fact that (Real.sqrt k - Real.sqrt ((k : ℝ) - 1)) > 0 to prove the inequality
          have h₁₀₈ : (1 : ℝ) / Real.sqrt k < 2 * (Real.sqrt k - Real.sqrt ((k : ℝ) - 1)) := by
            -- Use the identity involving square roots to prove the inequality
            have h₁₀₉ : (Real.sqrt k - Real.sqrt ((k : ℝ) - 1)) = 1 / (Real.sqrt k + Real.sqrt ((k : ℝ) - 1)) := by
              field_simp [h₁₀₅.ne']
              <;> nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) by linarith),
                Real.sq_sqrt (show 0 ≤ (k : ℝ) - 1 by linarith),
                mul_nonneg h₆ h₇, h₈.le, h₉.le]
            rw [h₁₀₉]
            have h₁₁₀ : (1 : ℝ) / Real.sqrt k < 2 * (1 / (Real.sqrt k + Real.sqrt ((k : ℝ) - 1))) := by
              have h₁₁₁ : 0 < Real.sqrt k + Real.sqrt ((k : ℝ) - 1) := by positivity
              have h₁₁₂ : 0 < Real.sqrt k * (Real.sqrt k + Real.sqrt ((k : ℝ) - 1)) := by positivity
              field_simp [h₁₁₁.ne']
              rw [div_lt_div_iff (by positivity) (by positivity)]
              nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) by linarith),
                Real.sq_sqrt (show 0 ≤ (k : ℝ) - 1 by linarith),
                mul_nonneg h₆ h₇, h₈.le, h₉.le]
            linarith
          linarith
        linarith
      linarith
    exact h₁₀
  
  have h₂ : (∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))) = 198 := by
    have h₃ : (∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))) = 2 * (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) := by
      -- Prove that the sum telescopes to 2 * (Real.sqrt 10000 - Real.sqrt 1)
      have h₄ : (∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))) = 2 * (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) := by
        -- Use the fact that the sum telescopes
        have h₅ : ∀ (n : ℕ), n ≥ 2 → (∑ k in Finset.Icc (2 : ℕ) n, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))) = 2 * (Real.sqrt (n : ℝ) - Real.sqrt (1 : ℝ)) := by
          intro n hn
          induction' hn with n hn IH
          · norm_num [Finset.sum_Icc_succ_top]
          · cases n with
            | zero => contradiction
            | succ n =>
              cases n with
              | zero => contradiction
              | succ n =>
                simp_all [Finset.sum_Icc_succ_top, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_succ]
                <;> ring_nf at *
                <;> field_simp at *
                <;> ring_nf at *
                <;> norm_num at *
                <;>
                (try
                  {
                    nlinarith [Real.sqrt_nonneg (n + 1 + 1 : ℝ), Real.sqrt_nonneg (n + 1 : ℝ),
                      Real.sqrt_nonneg (n + 1 + 1 - 1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 : ℝ) by positivity),
                      Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity),
                      Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 - 1 : ℝ) by
                        {
                          norm_num
                          <;> nlinarith
                        })]
                  })
                <;>
                (try
                  {
                    nlinarith [Real.sqrt_nonneg (n + 1 + 1 : ℝ), Real.sqrt_nonneg (n + 1 : ℝ),
                      Real.sqrt_nonneg (n + 1 + 1 - 1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 : ℝ) by positivity),
                      Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity),
                      Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 - 1 : ℝ) by
                        {
                          norm_num
                          <;> nlinarith
                        })]
                  })
                <;>
                (try
                  {
                    nlinarith [Real.sqrt_nonneg (n + 1 + 1 : ℝ), Real.sqrt_nonneg (n + 1 : ℝ),
                      Real.sqrt_nonneg (n + 1 + 1 - 1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 : ℝ) by positivity),
                      Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity),
                      Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 - 1 : ℝ) by
                        {
                          norm_num
                          <;> nlinarith
                        })]
                  })
        have h₆ : (∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))) = 2 * (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) := by
          apply h₅
          <;> norm_num
        rw [h₆]
      rw [h₄]
    rw [h₃]
    have h₄ : Real.sqrt (10000 : ℝ) = 100 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h₅ : Real.sqrt (1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h₄, h₅]
    <;> norm_num
  
  have h₃ : (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
    have h₄ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by
      have h₅ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < ∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) := by
        -- Prove that the sum of 1 / Real.sqrt k is less than the sum of the telescoping terms
        have h₅₁ : ∀ (k : ℕ), k ∈ Finset.Icc (2 : ℕ) 10000 → (1 : ℝ) / Real.sqrt k < 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) := by
          intro k hk
          exact h₁ k hk
        have h₅₂ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < ∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) := by
          -- Use the fact that each term is less than the corresponding telescoping term to prove the sum is less
          apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_of_ne_empty (by decide))
          intro k hk
          exact h₅₁ k hk
        simpa [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum] using h₅₂
      have h₅₃ : (∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))) = 198 := by
        exact h₂
      have h₅₄ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by
        linarith
      exact h₅₄
    exact h₄
  exact h₃