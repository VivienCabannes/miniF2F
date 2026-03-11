import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1973_p3 (a b : ℝ) (h₀ : ∃ x, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0) :
  4 / 5 ≤ a ^ 2 + b ^ 2 := by
  have h₁ : ∃ y, y ^ 2 + a * y + (b - 2) = 0 ∧ (y ≥ 2 ∨ y ≤ -2) := by
    obtain ⟨x, hx⟩ := h₀
    use (x ^ 2 + 1) / x
    constructor
    -- Show that the polynomial has a root in the form of (x^2 + 1) / x
    have hx1 : x ≠ 0 := by
      intro h
      rw [h] at hx
      norm_num at hx
    field_simp [hx1] at hx ⊢
    nlinarith [sq_nonneg (x ^ 2 + 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    -- Show that the root (y) must satisfy y ≥ 2 or y ≤ -2
    have hx1 : x ≠ 0 := by
      intro h
      rw [h] at hx
      norm_num at hx
    have hx2 : x > 0 ∨ x < 0 := by
      apply lt_or_gt_of_ne
      intro h
      rw [h] at hx1
      norm_num at hx1
    cases' hx2 with hx2 hx2
    · -- Case 1: x > 0
      apply or_iff_not_imp_left.mpr
      intro h
      -- Use the fact that x > 0 to show y ≥ 2
      have h1 : (x ^ 2 + 1) / x ≥ 2 := by
        -- Use the fact that x > 0 to show y ≥ 2
        apply (le_div_iff (by positivity)).mpr
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
      linarith
    · -- Case 2: x < 0
      apply or_iff_not_imp_right.mpr
      intro h
      -- Use the fact that x < 0 to show y ≤ -2
      have h1 : (x ^ 2 + 1) / x ≤ -2 := by
        -- Use the fact that x < 0 to show y ≤ -2
        apply (div_le_iff_of_neg (by linarith)).mpr
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
      linarith
  have h₂ : a ^ 2 - 4 * (b - 2) ≥ 0 := by
    obtain ⟨y, hy⟩ := h₁
    have h₂ := hy.2
    have h₃ := hy.1
    have h₄ : a ^ 2 - 4 * (b - 2) ≥ 0 := by
      cases' h₂ with h₂ h₂
      · nlinarith [sq_nonneg (y + 2), sq_nonneg (y - 2), sq_nonneg (a + 2 * y), sq_nonneg (a - 2 * y)]
      · nlinarith [sq_nonneg (y + 2), sq_nonneg (y - 2), sq_nonneg (a + 2 * y), sq_nonneg (a - 2 * y)]
    exact h₄
  
  have h₃ : a ^ 2 + b ^ 2 ≥ 4 / 5 := by
    obtain ⟨y, h_y, h_y_ineq⟩ := h₁
    have h_y_ineq' := h_y_ineq
    cases' h_y_ineq' with h_y_ge_2 h_y_le_neg_2 <;> simp_all
    <;> nlinarith [sq_nonneg (y + 2), sq_nonneg (y - 2), sq_nonneg a, sq_nonneg (b - 2),
      sq_nonneg (a - b * 2), sq_nonneg (a + b * 2), sq_nonneg (a ^ 2 - 4 * (b - 2))]
  have h₃' : a ^ 2 + b ^ 2 ≥ 4 / 5 := by assumption
  have h₂' : a ^ 2 - 4 * (b - 2) ≥ 0 := by assumption
  nlinarith [sq_nonneg (a ^ 2 - 4 * (b - 2))]