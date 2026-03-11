import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_33
  (x y z : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : 2 * x = 5 * y)
  (h₂ : 7 * y = 10 * z) :
  z / x = 7 / 25 := by
  have h₃ : 14 * x = 35 * y := by
    have h₃₁ : 14 * x = 35 * y := by
      have h₃₂ : 2 * x = 5 * y := h₁
      have h₃₃ : 7 * (2 * x) = 7 * (5 * y) := by rw [h₃₂]
      have h₃₄ : 7 * (2 * x) = 14 * x := by ring
      have h₃₅ : 7 * (5 * y) = 35 * y := by ring
      linarith
    exact h₃₁
  
  have h₄ : 35 * y = 50 * z := by
    have h₄₁ : 7 * y = 10 * z := h₂
    have h₄₂ : 5 * (7 * y) = 5 * (10 * z) := by rw [h₄₁]
    have h₄₃ : 5 * (7 * y) = 35 * y := by ring
    have h₄₄ : 5 * (10 * z) = 50 * z := by ring
    linarith
  
  have h₅ : 14 * x = 50 * z := by
    linarith
  
  have h₆ : z = (7 : ℝ) / 25 * x := by
    have h₆₁ : 14 * x = 50 * z := h₅
    have h₆₂ : z = (7 : ℝ) / 25 * x := by
      have h₆₃ : 50 * z = 14 * x := by linarith
      have h₆₄ : z = (14 : ℝ) / 50 * x := by
        -- Solve for z in terms of x
        apply mul_left_cancel₀ (show (50 : ℝ) ≠ 0 by norm_num)
        linarith
      -- Simplify the fraction 14/50 to 7/25
      have h₆₅ : z = (7 : ℝ) / 25 * x := by
        rw [h₆₄]
        <;> ring_nf at *
        <;> linarith
      exact h₆₅
    exact h₆₂
  
  have h₇ : z / x = 7 / 25 := by
    rw [h₆]
    have h₇₁ : (7 : ℝ) / 25 * x / x = 7 / 25 := by
      have h₇₂ : x ≠ 0 := h₀
      field_simp [h₇₂]
      <;> ring_nf
      <;> field_simp [h₇₂]
      <;> ring_nf
    rw [h₇₁]
  
  apply h₇