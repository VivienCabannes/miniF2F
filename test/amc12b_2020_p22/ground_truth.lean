import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2020_p22
  (t : ℝ) :
  ((2^t - 3 * t) * t) / (4^t) ≤ 1 / 12 := by
  have h₀ : ∀ (u : ℝ), u - 3 * u ^ 2 ≤ 1 / 12 := by
    intro u
    have h₁ : u - 3 * u ^ 2 ≤ 1 / 12 := by
      nlinarith [sq_nonneg (u - 1 / 6), sq_nonneg (u + 1 / 6), sq_nonneg (u - 1 / 3),
        sq_nonneg (u + 1 / 3), sq_nonneg (u - 1 / 2), sq_nonneg (u + 1 / 2),
        sq_nonneg (u - 1), sq_nonneg (u + 1), sq_nonneg (u - 2), sq_nonneg (u + 2)]
    exact h₁
  
  have h₁ : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
    have h₂ : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
      calc
        (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
          -- Use the property of exponents to rewrite 4^t as (2^2)^t = 2^(2*t)
          have h₃ : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
            calc
              (4 : ℝ) ^ t = ((2 : ℝ) ^ 2) ^ t := by norm_num
              _ = (2 : ℝ) ^ (2 * t) := by
                rw [← Real.rpow_nat_cast]
                rw [← Real.rpow_mul] <;> ring_nf <;> norm_num
                <;>
                linarith
              _ = (2 : ℝ) ^ (2 * t) := by rfl
          rw [h₃]
        _ = (2 : ℝ) ^ (2 * t) := by rfl
    exact h₂
  
  have h₂ : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by
    have h₃ : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := h₁
    have h₄ : (2 : ℝ) ^ (2 * t) = ((2 : ℝ) ^ t) ^ 2 := by
      calc
        (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ (t + t) := by ring
        _ = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by
          rw [Real.rpow_add] <;> ring_nf <;> norm_num
          <;>
          linarith
        _ = ((2 : ℝ) ^ t) ^ 2 := by ring
    rw [h₃, h₄]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h₃ : (2 ^ t - 3 * t) * t / 4 ^ t = (t / (2 : ℝ) ^ t - 3 * (t / (2 : ℝ) ^ t) ^ 2) := by
    have h₄ : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := h₂
    have h₅ : (4 : ℝ) ^ t > 0 := by positivity
    have h₆ : (2 : ℝ) ^ t > 0 := by positivity
    calc
      (2 ^ t - 3 * t) * t / 4 ^ t = ((2 : ℝ) ^ t - 3 * t) * t / 4 ^ t := by norm_num
      _ = ((2 : ℝ) ^ t - 3 * t) * t / ((2 : ℝ) ^ t) ^ 2 := by rw [h₄]
      _ = ((2 : ℝ) ^ t - 3 * t) * t / ((2 : ℝ) ^ t) ^ 2 := by ring
      _ = (t / (2 : ℝ) ^ t - 3 * (t / (2 : ℝ) ^ t) ^ 2) := by
        have h₇ : ((2 : ℝ) ^ t - 3 * t) * t / ((2 : ℝ) ^ t) ^ 2 = (t / (2 : ℝ) ^ t - 3 * (t / (2 : ℝ) ^ t) ^ 2) := by
          have h₈ : ((2 : ℝ) ^ t - 3 * t) * t / ((2 : ℝ) ^ t) ^ 2 = (t / (2 : ℝ) ^ t - 3 * (t / (2 : ℝ) ^ t) ^ 2) := by
            field_simp [h₆.ne']
            <;> ring_nf
            <;> field_simp [h₆.ne']
            <;> ring_nf
            <;> field_simp [h₆.ne']
            <;> ring_nf
          rw [h₈]
        rw [h₇]
      _ = (t / (2 : ℝ) ^ t - 3 * (t / (2 : ℝ) ^ t) ^ 2) := by ring
  
  have h₄ : (t / (2 : ℝ) ^ t - 3 * (t / (2 : ℝ) ^ t) ^ 2) ≤ 1 / 12 := by
    have h₅ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t) ^ 2 ≤ 1 / 12 := by
      have h₆ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t) ^ 2 ≤ 1 / 12 := by
        have h₇ : ∀ (u : ℝ), u - 3 * u ^ 2 ≤ 1 / 12 := h₀
        have h₈ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t) ^ 2 ≤ 1 / 12 := by
          apply h₇
        exact h₈
      exact h₆
    exact h₅
  
  have h₅ : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by
    rw [h₃]
    exact h₄
  
  exact h₅