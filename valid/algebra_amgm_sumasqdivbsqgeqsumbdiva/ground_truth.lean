import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbsqgeqsumbdiva (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ b / a + c / b + a / c := by
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b := mul_pos h₁ h₂
  have h₅ : 0 < b * c := mul_pos h₂ h₃
  have h₆ : 0 < c * a := mul_pos h₃ h₁
  field_simp [h₁.ne', h₂.ne', h₃.ne']
  rw [div_le_div_iff (by positivity) (by positivity)]
  ring_nf
  nlinarith [sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c),
    sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (b ^ 2 * c - c ^ 2 * a), sq_nonneg (c ^ 2 * a - a ^ 2 * b),
    mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁, mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃),
    mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁), mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]