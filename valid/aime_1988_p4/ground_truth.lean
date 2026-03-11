import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1988_p4 (n : ℕ) (a : ℕ → ℝ) (h₀ : ∀ n, abs (a n) < 1)
  (h₁ : (∑ k ∈ Finset.range n, abs (a k)) = 19 + abs (∑ k ∈ Finset.range n, a k)) : 20 ≤ n := by
  have h_S : ∑ k in Finset.range n, abs (a k) ≥ 0 := by
    -- Using the non-negativity property of absolute values, we can directly conclude that the sum of absolute values is non-negative.
    nlinarith [abs_nonneg (∑ k in Finset.range n, a k)]
  
  have h_triangle : abs (∑ k in Finset.range n, a k) ≤ ∑ k in Finset.range n, abs (a k) := by
    cases' le_total 0 (∑ k in Finset.range n, a k) with h h <;> simp_all [abs_of_nonneg, abs_of_nonpos, le_refl]
    <;> linarith
  
  have h_subst : ∑ k in Finset.range n, abs (a k) = 19 + abs (∑ k in Finset.range n, a k) := by
    -- Given the conditions, we directly use the equality provided in h₁ to conclude the proof.
    simpa [abs_le] using h₁
  
  have h_sum_ge_19 : ∑ k in Finset.range n, abs (a k) ≥ 19 := by
    -- We already have the equation S = 19 + |S| from the given conditions.
    have h₂ := h₁
    -- We need to show that S ≥ 19.
    -- From the equation S = 19 + |S|, we can rearrange to get |S| = S - 19.
    -- Since |S| ≥ 0, it follows that S - 19 ≥ 0, hence S ≥ 19.
    linarith [abs_nonneg (∑ k in Finset.range n, a k)]
  
  have h_need_20 : 20 ≤ n := by
    -- We will show that n must be at least 20 by contradiction.
    contrapose! h_sum_ge_19
    -- If n < 20, then the maximum possible sum of absolute values is bounded by the sum of the first 19 positive integers.
    interval_cases n <;> norm_num [Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos] at h₁ ⊢ <;>
      linarith [h₀ 0, h₀ 1, h₀ 2, h₀ 3, h₀ 4, h₀ 5, h₀ 6, h₀ 7, h₀ 8, h₀ 9, h₀ 10, h₀ 11, h₀ 12, h₀ 13,
        h₀ 14, h₀ 15, h₀ 16, h₀ 17, h₀ 18, h₀ 19]
  
  -- Since we have already established that n ≥ 20, we can directly conclude the proof.
  linarith