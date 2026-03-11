import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 3 ≤ a * b + b * c + c * a) :
  3 / Real.sqrt 2 ≤ a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) := by
  have h₂ : a + b + c ≥ 3 := by
    have h₂₁ : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h₂₂ : 3 * (a * b + b * c + c * a) ≥ 9 := by linarith
    have h₂₃ : (a + b + c) ^ 2 ≥ 9 := by linarith
    have h₂₄ : a + b + c ≥ 3 := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    exact h₂₄
  
  have h₃ : ∀ (x y : ℝ), 0 < x → 0 < y → Real.sqrt (x + y) ≤ (x + y + 2) / (2 * Real.sqrt 2) := by
    intro x y hx hy
    have h₄ : 0 < x + y := by linarith
    have h₅ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h₆ : 0 < Real.sqrt 2 * (x + y) := by positivity
    have h₇ : 0 < Real.sqrt 2 * 2 := by positivity
    have h₈ : Real.sqrt (x + y) ≤ (x + y + 2) / (2 * Real.sqrt 2) := by
      have h₈₁ : Real.sqrt (x + y) ≤ (x + y + 2) / (2 * Real.sqrt 2) := by
        rw [Real.sqrt_le_left (by positivity)]
        field_simp [h₅.ne']
        rw [le_div_iff (by positivity)]
        nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), sq_nonneg (x + y - 2),
          sq_nonneg (Real.sqrt 2 * Real.sqrt (x + y) - 2),
          Real.sq_sqrt (show 0 ≤ x + y by positivity), sq_nonneg (x + y - 2)]
      exact h₈₁
    exact h₈
  
  have h₄ : a / Real.sqrt (a + b) ≥ (2 * Real.sqrt 2 * a) / (a + b + 2) := by
    have h₄₁ : 0 < a := by linarith
    have h₄₂ : 0 < b := by linarith
    have h₄₃ : 0 < a + b := by linarith
    have h₄₄ : 0 < Real.sqrt (a + b) := Real.sqrt_pos.mpr h₄₃
    have h₄₅ : Real.sqrt (a + b) ≤ (a + b + 2) / (2 * Real.sqrt 2) := h₃ a b h₄₁ h₄₂
    have h₄₆ : a / Real.sqrt (a + b) ≥ a / ((a + b + 2) / (2 * Real.sqrt 2)) := by
      have h₄₇ : 0 < (a + b + 2) / (2 * Real.sqrt 2) := by positivity
      have h₄₈ : 0 < Real.sqrt (a + b) := Real.sqrt_pos.mpr h₄₃
      have h₄₉ : Real.sqrt (a + b) ≤ (a + b + 2) / (2 * Real.sqrt 2) := h₄₅
      have h₄₁₀ : a / Real.sqrt (a + b) ≥ a / ((a + b + 2) / (2 * Real.sqrt 2)) := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [Real.sqrt_nonneg (a + b), Real.sq_sqrt (show 0 ≤ a + b by positivity),
          Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      exact h₄₁₀
    have h₄₁₁ : a / ((a + b + 2) / (2 * Real.sqrt 2)) = (2 * Real.sqrt 2 * a) / (a + b + 2) := by
      field_simp [h₄₃.ne', Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> field_simp [h₄₃.ne', Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    rw [h₄₁₁] at h₄₆
    exact h₄₆
  
  have h₅ : b / Real.sqrt (b + c) ≥ (2 * Real.sqrt 2 * b) / (b + c + 2) := by
    have h₅₁ : 0 < b := by linarith
    have h₅₂ : 0 < c := by linarith
    have h₅₃ : 0 < b + c := by linarith
    have h₅₄ : 0 < Real.sqrt (b + c) := Real.sqrt_pos.mpr h₅₃
    have h₅₅ : Real.sqrt (b + c) ≤ (b + c + 2) / (2 * Real.sqrt 2) := h₃ b c h₅₁ h₅₂
    have h₅₆ : b / Real.sqrt (b + c) ≥ b / ((b + c + 2) / (2 * Real.sqrt 2)) := by
      have h₅₇ : 0 < (b + c + 2) / (2 * Real.sqrt 2) := by positivity
      have h₅₈ : 0 < Real.sqrt (b + c) := Real.sqrt_pos.mpr h₅₃
      have h₅₉ : Real.sqrt (b + c) ≤ (b + c + 2) / (2 * Real.sqrt 2) := h₅₅
      have h₅₁₀ : b / Real.sqrt (b + c) ≥ b / ((b + c + 2) / (2 * Real.sqrt 2)) := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [Real.sqrt_nonneg (b + c), Real.sq_sqrt (show 0 ≤ b + c by positivity),
          Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      exact h₅₁₀
    have h₅₁₁ : b / ((b + c + 2) / (2 * Real.sqrt 2)) = (2 * Real.sqrt 2 * b) / (b + c + 2) := by
      field_simp [h₅₃.ne', Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> field_simp [h₅₃.ne', Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    rw [h₅₁₁] at h₅₆
    exact h₅₆
  
  have h₆ : c / Real.sqrt (c + a) ≥ (2 * Real.sqrt 2 * c) / (c + a + 2) := by
    have h₆₁ : 0 < c := by linarith
    have h₆₂ : 0 < a := by linarith
    have h₆₃ : 0 < c + a := by linarith
    have h₆₄ : 0 < Real.sqrt (c + a) := Real.sqrt_pos.mpr h₆₃
    have h₆₅ : Real.sqrt (c + a) ≤ (c + a + 2) / (2 * Real.sqrt 2) := h₃ c a h₆₁ h₆₂
    have h₆₆ : c / Real.sqrt (c + a) ≥ c / ((c + a + 2) / (2 * Real.sqrt 2)) := by
      have h₆₇ : 0 < (c + a + 2) / (2 * Real.sqrt 2) := by positivity
      have h₆₈ : 0 < Real.sqrt (c + a) := Real.sqrt_pos.mpr h₆₃
      have h₆₉ : Real.sqrt (c + a) ≤ (c + a + 2) / (2 * Real.sqrt 2) := h₆₅
      have h₆₁₀ : c / Real.sqrt (c + a) ≥ c / ((c + a + 2) / (2 * Real.sqrt 2)) := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [Real.sqrt_nonneg (c + a), Real.sq_sqrt (show 0 ≤ c + a by positivity),
          Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      exact h₆₁₀
    have h₆₁₁ : c / ((c + a + 2) / (2 * Real.sqrt 2)) = (2 * Real.sqrt 2 * c) / (c + a + 2) := by
      field_simp [h₆₃.ne', Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> field_simp [h₆₃.ne', Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    rw [h₆₁₁] at h₆₆
    linarith
  
  have h₇ : a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) ≥ (2 * Real.sqrt 2 * a) / (a + b + 2) + (2 * Real.sqrt 2 * b) / (b + c + 2) + (2 * Real.sqrt 2 * c) / (c + a + 2) := by
    have h₇₁ : a / Real.sqrt (a + b) ≥ (2 * Real.sqrt 2 * a) / (a + b + 2) := h₄
    have h₇₂ : b / Real.sqrt (b + c) ≥ (2 * Real.sqrt 2 * b) / (b + c + 2) := h₅
    have h₇₃ : c / Real.sqrt (c + a) ≥ (2 * Real.sqrt 2 * c) / (c + a + 2) := h₆
    have h₇₄ : a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) ≥ (2 * Real.sqrt 2 * a) / (a + b + 2) + (2 * Real.sqrt 2 * b) / (b + c + 2) + (2 * Real.sqrt 2 * c) / (c + a + 2) := by
      linarith
    exact h₇₄
  
  have h₈ : (2 * Real.sqrt 2 * a) / (a + b + 2) + (2 * Real.sqrt 2 * b) / (b + c + 2) + (2 * Real.sqrt 2 * c) / (c + a + 2) ≥ 3 / Real.sqrt 2 := by
    have h₈₁ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h₈₂ : 0 < 2 * Real.sqrt 2 := by positivity
    have h₈₃ : 0 < a := by linarith
    have h₈₄ : 0 < b := by linarith
    have h₈₅ : 0 < c := by linarith
    have h₈₆ : 0 < a + b + 2 := by linarith
    have h₈₇ : 0 < b + c + 2 := by linarith
    have h₈₈ : 0 < c + a + 2 := by linarith
    have h₈₉ : 0 < (a + b + 2) * (b + c + 2) * (c + a + 2) := by positivity
    -- Use the fact that the sum of the fractions is at least 3/4
    have h₉₀ : a / (a + b + 2) + b / (b + c + 2) + c / (c + a + 2) ≥ 3 / 4 := by
      -- Use the symmetry and the given condition to prove the inequality
      have h₉₁ : 0 < a * b := by positivity
      have h₉₂ : 0 < b * c := by positivity
      have h₉₃ : 0 < c * a := by positivity
      field_simp
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    -- Use the result from h₉₀ to prove the final inequality
    have h₉₁ : (2 * Real.sqrt 2 * a) / (a + b + 2) + (2 * Real.sqrt 2 * b) / (b + c + 2) + (2 * Real.sqrt 2 * c) / (c + a + 2) = 2 * Real.sqrt 2 * (a / (a + b + 2) + b / (b + c + 2) + c / (c + a + 2)) := by
      field_simp [h₈₃.ne', h₈₄.ne', h₈₃.ne', h₈₄.ne', h₈₃.ne', h₈₄.ne']
      <;> ring_nf
      <;> field_simp [h₈₃.ne', h₈₄.ne', h₈₃.ne', h₈₄.ne', h₈₃.ne', h₈₄.ne']
      <;> ring_nf
      <;> nlinarith
    rw [h₉₁]
    have h₉₂ : 2 * Real.sqrt 2 * (a / (a + b + 2) + b / (b + c + 2) + c / (c + a + 2)) ≥ 2 * Real.sqrt 2 * (3 / 4) := by
      gcongr
      <;> linarith
    have h₉₃ : 2 * Real.sqrt 2 * (3 / 4) = 3 / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt 2 / 2) := by
      field_simp [Real.sqrt_eq_iff_sq_eq, mul_comm]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq, mul_comm]
      <;> nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    have h₉₄ : 3 / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt 2 / 2) = 3 / Real.sqrt 2 * (1) := by
      have h₉₅ : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      rw [h₉₅]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq, mul_comm]
      <;> nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    have h₉₅ : 3 / Real.sqrt 2 * (1 : ℝ) = 3 / Real.sqrt 2 := by
      ring
    have h₉₆ : 2 * Real.sqrt 2 * (3 / 4) ≥ 3 / Real.sqrt 2 := by
      have h₉₇ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have h₉₈ : 0 < Real.sqrt 2 ^ 2 := by positivity
      field_simp [h₉₇.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    linarith
  
  have h₉ : 3 / Real.sqrt 2 ≤ a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) := by
    have h₉₁ : a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) ≥ (2 * Real.sqrt 2 * a) / (a + b + 2) + (2 * Real.sqrt 2 * b) / (b + c + 2) + (2 * Real.sqrt 2 * c) / (c + a + 2) := h₇
    have h₉₂ : (2 * Real.sqrt 2 * a) / (a + b + 2) + (2 * Real.sqrt 2 * b) / (b + c + 2) + (2 * Real.sqrt 2 * c) / (c + a + 2) ≥ 3 / Real.sqrt 2 := h₈
    linarith
  
  linarith