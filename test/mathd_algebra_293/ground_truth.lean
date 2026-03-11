import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_293
  (x : NNReal) :
  Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have h₀ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ))) := by
    have h₁ : Real.sqrt (60 * (x : ℝ)) * Real.sqrt (12 * (x : ℝ)) * Real.sqrt (63 * (x : ℝ)) = Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ))) := by
      have h₂ : 0 ≤ (60 : ℝ) * (x : ℝ) := by positivity
      have h₃ : 0 ≤ (12 : ℝ) * (x : ℝ) := by positivity
      have h₄ : 0 ≤ (63 : ℝ) * (x : ℝ) := by positivity
      have h₅ : 0 ≤ (60 : ℝ) * (x : ℝ) * (12 * (x : ℝ)) := by positivity
      have h₆ : 0 ≤ (60 : ℝ) * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ)) := by positivity
      have h₇ : Real.sqrt (60 * (x : ℝ)) * Real.sqrt (12 * (x : ℝ)) = Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ))) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h₇]
      have h₈ : Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ))) * Real.sqrt (63 * (x : ℝ)) = Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ))) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h₈]
    have h₉ : Real.sqrt (60 * x) = Real.sqrt (60 * (x : ℝ)) := by simp [Real.sqrt_eq_iff_sq_eq]
    have h₁₀ : Real.sqrt (12 * x) = Real.sqrt (12 * (x : ℝ)) := by simp [Real.sqrt_eq_iff_sq_eq]
    have h₁₁ : Real.sqrt (63 * x) = Real.sqrt (63 * (x : ℝ)) := by simp [Real.sqrt_eq_iff_sq_eq]
    rw [h₉, h₁₀, h₁₁]
    exact h₁
  
  have h₁ : Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ))) = Real.sqrt (45360 * (x : ℝ)^3) := by
    have h₁₀ : (60 : ℝ) * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ)) = 45360 * (x : ℝ) ^ 3 := by
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> norm_cast
      <;> simp [mul_assoc]
      <;> ring_nf
      <;> norm_num
      <;> nlinarith
    rw [h₁₀]
    <;>
    simp [Real.sqrt_eq_iff_sq_eq]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h₂ : Real.sqrt (45360 * (x : ℝ)^3) = Real.sqrt ((36 : ℝ)^2 * 35 * (x : ℝ)^3) := by
    have h₂₁ : (45360 : ℝ) * (x : ℝ) ^ 3 = (36 : ℝ) ^ 2 * 35 * (x : ℝ) ^ 3 := by
      ring_nf
      <;> norm_num
      <;>
      simp [mul_assoc]
      <;>
      ring_nf
      <;>
      norm_num
      <;>
      nlinarith
    rw [h₂₁]
    <;>
    simp [Real.sqrt_eq_iff_sq_eq]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h₃ : Real.sqrt ((36 : ℝ)^2 * 35 * (x : ℝ)^3) = 36 * Real.sqrt (35 * (x : ℝ)^3) := by
    have h₃₁ : 0 ≤ (36 : ℝ) := by positivity
    have h₃₂ : 0 ≤ (35 : ℝ) * (x : ℝ) ^ 3 := by positivity
    have h₃₃ : 0 ≤ (x : ℝ) := by positivity
    have h₃₄ : 0 ≤ (x : ℝ) ^ 3 := by positivity
    have h₃₅ : 0 ≤ (35 : ℝ) * (x : ℝ) ^ 3 := by positivity
    have h₃₆ : Real.sqrt ((36 : ℝ) ^ 2 * 35 * (x : ℝ) ^ 3) = 36 * Real.sqrt (35 * (x : ℝ) ^ 3) := by
      rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)]
      have h₃₇ : (36 : ℝ) ^ 2 = 1296 := by norm_num
      have h₃₈ : (36 : ℝ) ^ 2 * 35 * (x : ℝ) ^ 3 = (36 : ℝ) ^ 2 * (35 * (x : ℝ) ^ 3) := by ring
      rw [h₃₈]
      have h₃₉ : Real.sqrt (35 * (x : ℝ) ^ 3) ≥ 0 := Real.sqrt_nonneg _
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 35 * (x : ℝ) ^ 3)]
    rw [h₃₆]
    <;>
    simp [h₃₁, h₃₂, h₃₃, h₃₄, h₃₅]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h₄ : Real.sqrt (35 * (x : ℝ)^3) = (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
    have h₄₁ : 0 ≤ (x : ℝ) := by exact_mod_cast x.prop
    have h₄₂ : Real.sqrt (35 * (x : ℝ) ^ 3) = (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
      have h₄₃ : Real.sqrt (35 * (x : ℝ) ^ 3) = Real.sqrt (35 * (x : ℝ) * (x : ℝ) ^ 2) := by
        ring_nf
        <;> field_simp <;> ring_nf
      rw [h₄₃]
      have h₄₄ : Real.sqrt (35 * (x : ℝ) * (x : ℝ) ^ 2) = (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
        have h₄₅ : 0 ≤ (x : ℝ) ^ 2 := by positivity
        have h₄₆ : 0 ≤ 35 * (x : ℝ) := by positivity
        have h₄₇ : 0 ≤ 35 * (x : ℝ) * (x : ℝ) ^ 2 := by positivity
        have h₄₈ : Real.sqrt (35 * (x : ℝ) * (x : ℝ) ^ 2) = (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
          rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)]
          nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (35 : ℝ) * (x : ℝ)), mul_self_nonneg (x : ℝ),
            mul_nonneg h₄₁ (sq_nonneg (x : ℝ))]
        rw [h₄₈]
      rw [h₄₄]
    rw [h₄₂]
    <;>
    simp_all [Real.sqrt_eq_iff_sq_eq]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h₅ : 36 * Real.sqrt (35 * (x : ℝ)^3) = 36 * (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
    rw [h₄]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  
  have h₆ : Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ))) = 36 * (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
    rw [h₁]
    rw [h₂]
    rw [h₃]
    rw [h₅]
    <;>
    simp_all [mul_assoc]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h₇ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
    have h₇₁ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ))) := by
      exact h₀
    rw [h₇₁]
    have h₇₂ : Real.sqrt (60 * (x : ℝ) * (12 * (x : ℝ)) * (63 * (x : ℝ))) = 36 * (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
      exact h₆
    rw [h₇₂]
    <;>
    norm_cast
    <;>
    field_simp [Real.sqrt_eq_iff_sq_eq]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    nlinarith
  
  exact h₇