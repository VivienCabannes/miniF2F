import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1964_p2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  have h₄ : 0 < b + c - a := by
    linarith
  
  have h₅ : 0 < c + a - b := by
    linarith
  
  have h₆ : 0 < a + b - c := by
    linarith
  
  have h₇ : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by
    have h₇₁ : 0 < b + c - a := h₄
    have h₇₂ : 0 < c + a - b := h₅
    have h₇₃ : 0 < a + b - c := h₆
    have h₇₄ : 0 < (b + c - a) * (c + a - b) := by positivity
    have h₇₅ : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by positivity
    exact h₇₅
  
  have h₈ : (b + c - a) * (c + a - b) * (a + b - c) ≤ a * b * c := by
    have h₈₁ : 0 < a := by linarith
    have h₈₂ : 0 < b := by linarith
    have h₈₃ : 0 < c := by linarith
    have h₈₄ : 0 < a * b := by positivity
    have h₈₅ : 0 < b * c := by positivity
    have h₈₆ : 0 < c * a := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (b + c - a - c), sq_nonneg (c + a - b - a), sq_nonneg (a + b - c - b),
      mul_pos h₄ h₅, mul_pos h₅ h₆, mul_pos h₆ h₄,
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
      mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁)]
  
  have h₉ : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) = (b + c - a) * (c + a - b) * (a + b - c) + 2 * a * b * c := by
    have h₉₁ : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) = (b + c - a) * (c + a - b) * (a + b - c) + 2 * a * b * c := by
      ring_nf at *
      <;>
      nlinarith [h₀.1, h₀.2.1, h₀.2.2, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈,
        mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.1 h₀.2.2]
    rw [h₉₁]
    <;>
    nlinarith
  
  have h₁₀ : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
    rw [h₉]
    have h₁₀₁ : 0 < a * b * c := by
      have h₁₀₂ : 0 < a * b := by nlinarith
      have h₁₀₃ : 0 < b * c := by nlinarith
      have h₁₀₄ : 0 < c * a := by nlinarith
      nlinarith
    nlinarith [h₈]
  
  exact h₁₀