import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1962_p2
  (x : ℝ)
  (h₀ : 0 ≤ 3 - x)
  (h₁ : 0 ≤ x + 1)
  (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) :
  -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  have h₃ : -1 ≤ x := by
    linarith
  
  have h₄ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 2 := by
    linarith
  
  have h₅ : Real.sqrt (3 - x) > Real.sqrt (x + 1) + 1 / 2 := by
    linarith
  
  have h₆ : 3 - x > x + 1 + Real.sqrt (x + 1) + 1 / 4 := by
    have h₆₁ : Real.sqrt (3 - x) > Real.sqrt (x + 1) + 1 / 2 := h₅
    have h₆₂ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
    have h₆₃ : 0 ≤ Real.sqrt (3 - x) := Real.sqrt_nonneg (3 - x)
    have h₆₄ : 0 ≤ Real.sqrt (x + 1) * (1 / 2) := by positivity
    have h₆₅ : 0 ≤ Real.sqrt (3 - x) := Real.sqrt_nonneg (3 - x)
    have h₆₆ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
    have h₆₇ : (Real.sqrt (x + 1) + 1 / 2) ≥ 0 := by positivity
    have h₆₈ : Real.sqrt (3 - x) > Real.sqrt (x + 1) + 1 / 2 := h₅
    have h₆₉ : (Real.sqrt (x + 1) + 1 / 2) ^ 2 < (Real.sqrt (3 - x)) ^ 2 := by
      gcongr
      <;> nlinarith [Real.sq_sqrt (show 0 ≤ x + 1 by linarith), Real.sq_sqrt (show 0 ≤ 3 - x by linarith)]
    have h₆₁₀ : (Real.sqrt (x + 1) + 1 / 2) ^ 2 = (x + 1) + Real.sqrt (x + 1) + 1 / 4 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ x + 1 by linarith), Real.sq_sqrt (show 0 ≤ 3 - x by linarith),
        sq_nonneg (Real.sqrt (x + 1) - 1 / 2)]
    have h₆₁₁ : (Real.sqrt (3 - x)) ^ 2 = 3 - x := by
      rw [Real.sq_sqrt] <;> linarith
    nlinarith [Real.sq_sqrt (show 0 ≤ x + 1 by linarith), Real.sq_sqrt (show 0 ≤ 3 - x by linarith)]
  
  have h₇ : 7 - 8 * x > 4 * Real.sqrt (x + 1) := by
    have h₇₁ : 3 - x > x + 1 + Real.sqrt (x + 1) + 1 / 4 := h₆
    have h₇₂ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
    nlinarith [Real.sqrt_nonneg (x + 1)]
  
  have h₈ : x < 7 / 8 := by
    by_contra h
    have h₈₁ : x ≥ 7 / 8 := by linarith
    have h₈₂ : 7 - 8 * x ≤ 0 := by
      linarith
    have h₈₃ : 4 * Real.sqrt (x + 1) ≥ 0 := by positivity
    linarith
  
  have h₉ : 0 ≤ Real.sqrt 31 := by positivity
  
  have h₁₀ : 64 * x ^ 2 - 128 * x + 33 > 0 := by
    have h₁₀₁ : 7 - 8 * x > 4 * Real.sqrt (x + 1) := h₇
    have h₁₀₂ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
    have h₁₀₃ : 0 ≤ 7 - 8 * x := by linarith
    have h₁₀₄ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
    have h₁₀₅ : 0 ≤ 7 - 8 * x := by linarith
    have h₁₀₆ : (7 - 8 * x) ^ 2 > (4 * Real.sqrt (x + 1)) ^ 2 := by
      gcongr
    have h₁₀₇ : (4 * Real.sqrt (x + 1)) ^ 2 = 16 * (x + 1) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ x + 1 by linarith), sq_nonneg (Real.sqrt (x + 1) - 2)]
    have h₁₀₈ : (7 - 8 * x) ^ 2 > 16 * (x + 1) := by
      linarith
    nlinarith [Real.sq_sqrt (show 0 ≤ x + 1 by linarith), sq_nonneg (x - 1)]
  
  have h₁₁ : x < 1 - Real.sqrt 31 / 8 := by
    by_contra h
    have h₁₁₁ : x ≥ 1 - Real.sqrt 31 / 8 := by
      linarith
    have h₁₁₂ : 64 * x ^ 2 - 128 * x + 33 ≤ 0 := by
      have h₁₁₃ : x ≥ 1 - Real.sqrt 31 / 8 := h₁₁₁
      have h₁₁₄ : x ≤ 1 + Real.sqrt 31 / 8 := by
        by_contra h₁₁₄
        have h₁₁₅ : x > 1 + Real.sqrt 31 / 8 := by linarith
        have h₁₁₆ : 64 * x ^ 2 - 128 * x + 33 > 0 := h₁₀
        have h₁₁₇ : x < 7 / 8 := h₈
        nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num)]
      nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num),
        sq_nonneg (x - (1 - Real.sqrt 31 / 8)), sq_nonneg (x - (1 + Real.sqrt 31 / 8))]
    linarith [h₁₀]
  
  exact ⟨h₃, h₁₁⟩