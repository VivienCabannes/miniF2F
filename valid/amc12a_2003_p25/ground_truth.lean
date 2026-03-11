import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2003_p25 (a b : ℝ) (f : ℝ → ℝ) (h₀ : 0 < b)
  (h₁ : ∀ x, f x = Real.sqrt (a * x ^ 2 + b * x)) (h₂ : { x | 0 ≤ f x } = f '' { x | 0 ≤ f x }) :
  a = 0 ∨ a = -4 := by
  have h₃ := h₂
  simp only [Set.ext_iff, h₁, Set.mem_setOf_eq, Set.mem_image, Real.sqrt_nonneg] at h₃
  have h₄ := h₃ 0
  have h₅ := h₃ 1
  have h₆ := h₃ (-1)
  have h₇ := h₃ 2
  have h₈ := h₃ (-2)
  simp at h₄ h₅ h₆ h₇ h₈
  have h₉ := h₅
  simp at h₉
  have h₁₀ := h₆
  simp at h₁₀
  cases' h₄ with x hx
  cases' h₇ with x hx
  cases' h₈ with x hx
  nlinarith [Real.sqrt_nonneg (a * x ^ 2 + b * x), Real.sqrt_nonneg (a * 2 ^ 2 + b * 2),
    Real.sqrt_nonneg (a * (-2) ^ 2 + b * (-2)), Real.sqrt_nonneg (a * 1 ^ 2 + b * 1),
    Real.sqrt_nonneg (a * (-1) ^ 2 + b * (-1))]