import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
  have h₂ : 0 < a := by linarith
  have h₃ : 0 < b := by linarith
  have h₄ : 0 < Real.sqrt a := Real.sqrt_pos.mpr h₂
  have h₅ : 0 < Real.sqrt b := Real.sqrt_pos.mpr h₃
  have h₆ : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt h₁
  set x := Real.sqrt a
  set y := Real.sqrt b
  have h₇ : x ≥ y := h₆
  have h₈ : 0 < y := h₅
  have h₉ : 0 < x := h₄
  have h₁₀ : (a + b) / 2 - Real.sqrt (a * b) = (x - y)^2 / 2 := by
    have h₁₀₁ : a = x ^ 2 := by
      rw [← Real.sq_sqrt (le_of_lt h₂)]
      <;> simp [x]
    have h₁₀₂ : b = y ^ 2 := by
      rw [← Real.sq_sqrt (le_of_lt h₃)]
      <;> simp [y]
    rw [h₁₀₁, h₁₀₂]
    have h₁₀₃ : Real.sqrt ((x ^ 2) * (y ^ 2)) = x * y := by
      rw [show x ^ 2 * y ^ 2 = (x * y) ^ 2 from by ring]
      exact Real.sqrt_sq (by positivity : (0 : ℝ) ≤ x * y)
    have h₁₀₄ : (x ^ 2 + y ^ 2) / 2 - Real.sqrt ((x ^ 2) * (y ^ 2)) = (x - y) ^ 2 / 2 := by
      rw [h₁₀₃]
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> nlinarith [sq_nonneg (x - y)]
    rw [h₁₀₄]
    <;> ring_nf
  
  have h₁₁ : (a - b)^2 / (8 * b) = (x - y)^2 * (x + y)^2 / (8 * y^2) := by
    have h₁₁₁ : a = x ^ 2 := by
      rw [← Real.sq_sqrt (le_of_lt h₂)]
      <;> simp [x]
    have h₁₁₂ : b = y ^ 2 := by
      rw [← Real.sq_sqrt (le_of_lt h₃)]
      <;> simp [y]
    rw [h₁₁₁, h₁₁₂]
    have h₁₁₃ : (x ^ 2 - y ^ 2) ^ 2 = (x - y) ^ 2 * (x + y) ^ 2 := by
      ring_nf
      <;>
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    rw [h₁₁₃]
    <;> field_simp [h₃.ne', h₂.ne', h₈.ne', h₉.ne']
    <;> ring_nf
    <;> field_simp [h₃.ne', h₂.ne', h₈.ne', h₉.ne']
    <;> ring_nf
    <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  
  have h₁₂ : (x - y)^2 / 2 ≤ (x - y)^2 * (x + y)^2 / (8 * y^2) := by
    have h₁₂₁ : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    have h₁₂₂ : 0 < y := h₈
    have h₁₂₃ : 0 < x := h₉
    have h₁₂₄ : 0 < y ^ 2 := by positivity
    have h₁₂₅ : 0 < x ^ 2 := by positivity
    have h₁₂₆ : 4 * y ^ 2 ≤ (x + y) ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 3 * y),
        sq_nonneg (x + 3 * y)]
    have h₁₂₇ : (x - y) ^ 2 / 2 ≤ (x - y) ^ 2 * (x + y) ^ 2 / (8 * y ^ 2) := by
      by_cases h : (x - y) ^ 2 = 0
      · rw [h]
        <;> simp
        <;> positivity
      · have h₁₂₈ : 0 < (x - y) ^ 2 := by positivity
        have h₁₂₉ : 4 * y ^ 2 ≤ (x + y) ^ 2 := h₁₂₆
        have h₁₃₀ : 0 < 8 * y ^ 2 := by positivity
        have h₁₃₁ : 0 < (x - y) ^ 2 * (x + y) ^ 2 := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 3 * y),
          sq_nonneg (x + 3 * y)]
    exact h₁₂₇
  
  have h₁₃ : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
    rw [h₁₀, h₁₁]
    <;> linarith
  
  exact h₁₃