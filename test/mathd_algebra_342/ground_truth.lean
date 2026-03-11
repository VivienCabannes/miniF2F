import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_342
  (a d: ℝ)
  (h₀ : ∑ k ∈ (Finset.range 5), (a + k * d) = 70)
  (h₁ : ∑ k ∈ (Finset.range 10), (a + k * d) = 210) :
  a = 42/5 := by
  have h₂ : 5 * a + 10 * d = 70 := by
    have h₂₁ : (∑ k in Finset.range 5, (a + k * d : ℝ)) = 5 * a + 10 * d := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      <;> ring_nf
      <;> norm_num
      <;> linarith
    rw [h₂₁] at h₀
    linarith
  
  have h₃ : 10 * a + 45 * d = 210 := by
    have h₃₁ : (∑ k in Finset.range 10, (a + k * d : ℝ)) = 10 * a + 45 * d := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      <;> ring_nf
      <;> norm_num
      <;> linarith
    rw [h₃₁] at h₁
    linarith
  
  have h₄ : a + 2 * d = 14 := by
    have h₄₁ : 5 * a + 10 * d = 70 := h₂
    have h₄₂ : a + 2 * d = 14 := by
      have h₄₃ : 5 * a + 10 * d = 70 := h₂
      have h₄₄ : a + 2 * d = 14 := by
        linarith
      exact h₄₄
    exact h₄₂
  
  have h₅ : 2 * a + 9 * d = 42 := by
    have h₅₁ : 2 * a + 9 * d = 42 := by
      linarith
    exact h₅₁
  
  have h₆ : d = 14 / 5 := by
    have h₆₁ : d = 14 / 5 := by
      have h₆₂ : 5 * d = 14 := by
        linarith
      linarith
    exact h₆₁
  
  have h₇ : a = 42 / 5 := by
    have h₇₁ : a = 42 / 5 := by
      have h₇₂ : a + 2 * d = 14 := h₄
      have h₇₃ : d = 14 / 5 := h₆
      rw [h₇₃] at h₇₂
      ring_nf at h₇₂ ⊢
      linarith
    exact h₇₁
  
  apply h₇