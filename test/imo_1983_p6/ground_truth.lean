import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have h₄ : 0 < b + c - a := by
    linarith [h₃]
    <;> linarith
  
  have h₅ : 0 < c + a - b := by
    linarith [h₂]
    <;> linarith
  
  have h₆ : 0 < a + b - c := by
    linarith [h₁]
    <;> linarith
  
  have h₇ : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
    have h₇₁ : 0 < a := by linarith
    have h₇₂ : 0 < b := by linarith
    have h₇₃ : 0 < c := by linarith
    have h₇₄ : 0 < a * b := by positivity
    have h₇₅ : 0 < b * c := by positivity
    have h₇₆ : 0 < c * a := by positivity
    -- Use nlinarith to prove the inequality by leveraging the properties of the terms
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.2.2 h₀.1,
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
      mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁), mul_pos h₄ h₅, mul_pos h₅ h₆,
      mul_pos h₆ h₄, sq_nonneg (a - b + c), sq_nonneg (b - c + a),
      sq_nonneg (c - a + b), mul_nonneg (sub_nonneg.mpr h₁.le) (sub_nonneg.mpr h₂.le),
      mul_nonneg (sub_nonneg.mpr h₂.le) (sub_nonneg.mpr h₃.le),
      mul_nonneg (sub_nonneg.mpr h₃.le) (sub_nonneg.mpr h₁.le)]
  
  exact h₇