import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by
  -- Set a = x² - 10x to reduce the problem to linear algebra
  set a := x ^ 2 - 10 * x with ha_def
  -- After set, h₁ : a - 29 ≠ 0, h₂ : a - 45 ≠ 0, h₃ : a - 69 ≠ 0
  -- h₄ : 1/(a-29) + 1/(a-45) - 2/(a-69) = 0
  have ha : a = 39 := by
    have h5 := h₄
    field_simp [h₁, h₂, h₃] at h5
    nlinarith
  -- Now a = 39 means x² - 10x = 39, i.e., x² - 10x - 39 = 0
  have hq : x ^ 2 - 10 * x - 39 = 0 := by linarith [ha_def ▸ ha]
  have hfact : (x - 13) * (x + 3) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith [h₀]
