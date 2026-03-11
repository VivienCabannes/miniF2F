import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h₃ : 0 ≤ a := by
    by_contra h
    have h₄ : a < 0 := by linarith
    have h₅ : a * (4 - 3 * a) < 0 := by
      have h₅₁ : 4 - 3 * a > 0 := by nlinarith
      nlinarith
    have h₆ : (b - c) ^ 2 = 4 * a - 3 * a ^ 2 := by
      have h₆₁ : a ^ 2 + b ^ 2 + c ^ 2 = 2 := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have h₆₂ : a * b + b * c + c * a = 1 := h₂
      nlinarith [sq_nonneg (b - c)]
    have h₇ : (b - c) ^ 2 ≥ 0 := sq_nonneg (b - c)
    nlinarith [sq_nonneg (b - c)]
  
  have h₄ : 1 ≤ c := by
    have h₄₁ : a ≤ b := h₀.1
    have h₄₂ : b ≤ c := h₀.2
    have h₄₃ : a + b + c = 2 := h₁
    have h₄₄ : a * b + b * c + c * a = 1 := h₂
    by_contra! h
    have h₅ : c < 1 := by linarith
    have h₆ : a + b = 2 - c := by linarith
    have h₇ : a * b = 1 - c * (a + b) := by
      nlinarith
    have h₈ : a * b = (c - 1) ^ 2 := by
      rw [h₆] at h₇
      nlinarith
    have h₉ : (b - c) ^ 2 ≥ 0 := by nlinarith
    have h₁₀ : (2 - c) ^ 2 - 4 * (c - 1) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
    have h₁₁ : c ≥ 2 / 3 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
    have h₁₂ : 3 * c ^ 2 - 4 * c + 1 ≤ 0 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
    have h₁₃ : c ≤ 1 := by nlinarith
    have h₁₄ : c ≥ 2 / 3 := by nlinarith
    have h₁₅ : b ≤ c := h₀.2
    have h₁₆ : a ≤ b := h₀.1
    have h₁₇ : (2 - c) ^ 2 - 4 * (c - 1) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
    have h₁₈ : 3 * c ^ 2 - 4 * c + 1 ≤ 0 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
    have h₁₉ : c ≥ 1 := by
      by_contra h₂₀
      have h₂₁ : c < 1 := by linarith
      have h₂₂ : (2 - c) ^ 2 - 4 * (c - 1) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
      have h₂₃ : 3 * c ^ 2 - 4 * c + 1 ≤ 0 := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
      have h₂₄ : c ≥ 2 / 3 := by nlinarith
      have h₂₅ : c ≤ 1 := by nlinarith
      have h₂₆ : b ≤ c := h₀.2
      have h₂₇ : a ≤ b := h₀.1
      have h₂₈ : (2 - c) ^ 2 - 4 * (c - 1) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
      have h₂₉ : 3 * c ^ 2 - 4 * c + 1 ≤ 0 := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
      by_cases h₃₀ : c ≥ 1
      · linarith
      · have h₃₁ : c < 1 := by linarith
        have h₃₂ : 3 * c ^ 2 - 4 * c + 1 > 0 := by
          nlinarith [sq_nonneg (c - 1 / 3), sq_nonneg (c - 2 / 3)]
        linarith
    linarith
  
  have h₅ : c ≤ 4 / 3 := by
    have h₅₁ : a + b + c = 2 := h₁
    have h₅₂ : a * b + b * c + c * a = 1 := h₂
    have h₅₃ : a ≤ b := h₀.1
    have h₅₄ : b ≤ c := h₀.2
    have h₅₅ : 0 ≤ a := h₃
    have h₅₆ : 1 ≤ c := h₄
    have h₅₇ : (b - c) ^ 2 ≥ 0 := by nlinarith
    have h₅₈ : c ≤ 4 / 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_nonneg (sub_nonneg.mpr h₅₅) (sub_nonneg.mpr h₅₃),
        mul_nonneg (sub_nonneg.mpr h₅₃) (sub_nonneg.mpr h₅₄),
        mul_nonneg (sub_nonneg.mpr h₅₅) (sub_nonneg.mpr h₅₄)]
    exact h₅₈
    <;> linarith
  
  have h₆ : a ≤ 1 / 3 := by
    have h₆₁ : a + b = 2 - c := by linarith
    have h₆₂ : a * b = (c - 1) ^ 2 := by
      have h₆₃ : a * b + b * c + c * a = 1 := h₂
      have h₆₄ : a + b + c = 2 := h₁
      have h₆₅ : a * b = 1 - c * (a + b) := by
        nlinarith
      rw [h₆₁] at h₆₅
      nlinarith
    have h₆₃ : c ≥ 1 := h₄
    have h₆₄ : c ≤ 4 / 3 := h₅
    have h₆₅ : a ≤ 1 / 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₀.1),
        mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2),
        mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₀.2)]
    exact h₆₅
  
  have h₇ : 1 / 3 ≤ b := by
    have h₇₁ : a + b = 2 - c := by linarith
    have h₇₂ : c ≤ 4 / 3 := h₅
    have h₇₃ : 1 ≤ c := h₄
    have h₇₄ : a ≤ b := h₀.1
    have h₇₅ : 0 ≤ a := h₃
    have h₇₆ : 1 / 3 ≤ b := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    exact h₇₆
  
  have h₈ : b ≤ 1 := by
    have h₈₁ : a + b + c = 2 := h₁
    have h₈₂ : a * b + b * c + c * a = 1 := h₂
    have h₈₃ : a ≤ b := h₀.1
    have h₈₄ : b ≤ c := h₀.2
    have h₈₅ : 0 ≤ a := h₃
    have h₈₆ : 1 ≤ c := h₄
    have h₈₇ : c ≤ 4 / 3 := h₅
    have h₈₈ : a ≤ 1 / 3 := h₆
    have h₈₉ : 1 / 3 ≤ b := h₇
    -- Use nlinarith to prove b ≤ 1
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₉ : 0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
    exact ⟨h₃, h₆, h₇, h₈, h₄, h₅⟩
  
  exact h₉