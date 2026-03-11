import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_480 (f : ℝ → ℝ) (h₀ : ∀ x < 0, f x = -x ^ 2 - 1)
  (h₁ : ∀ x, 0 ≤ x ∧ x < 4 → f x = 2) (h₂ : ∀ x ≥ 4, f x = Real.sqrt x) : f π = 2 := by
  have h : Real.pi ≥ 0 := Real.pi_pos.le
  by_cases h₁ : Real.pi < 4
  <;> by_cases h₂ : Real.pi < 0
  <;> by_cases h₃ : Real.pi ≥ 4
  <;> simp_all [h₀, h₁, h₂, h₃, Real.sqrt_eq_iff_sq_eq]
  <;> nlinarith [Real.pi_le_four]
  <;> nlinarith [Real.pi_pos]
  <;> nlinarith [Real.pi_le_four]
  <;> nlinarith [Real.pi_pos]