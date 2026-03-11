import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_441
  (x : ℝ)
  (h₀ : x ≠ 0) :
  12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  have h₁ : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = (12 * x ^ 4 * 35) / ((x * x) * (14 * x) * (3 * x)) := by
    have h₁₁ : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = (12 / (x * x)) * ((x ^ 4 / (14 * x)) * (35 / (3 * x))) := by
      ring
    rw [h₁₁]
    have h₁₂ : (x ^ 4 / (14 * x)) * (35 / (3 * x)) = (x ^ 4 * 35) / ((14 * x) * (3 * x)) := by
      field_simp [h₀, pow_ne_zero, mul_comm, mul_assoc, mul_left_comm]
      <;> ring_nf
      <;> field_simp [h₀, pow_ne_zero]
      <;> ring_nf
    rw [h₁₂]
    have h₁₃ : (12 / (x * x)) * ((x ^ 4 * 35) / ((14 * x) * (3 * x))) = (12 * x ^ 4 * 35) / ((x * x) * (14 * x) * (3 * x)) := by
      field_simp [h₀, pow_ne_zero, mul_comm, mul_assoc, mul_left_comm]
      <;> ring_nf
      <;> field_simp [h₀, pow_ne_zero]
      <;> ring_nf
    rw [h₁₃]
    <;> ring_nf
  
  have h₂ : (x * x) * (14 * x) * (3 * x) = 42 * x ^ 4 := by
    have h₂₁ : (x * x) * (14 * x) * (3 * x) = 42 * x ^ 4 := by
      ring_nf
      <;>
      simp_all [mul_assoc, mul_comm, mul_left_comm]
      <;>
      ring_nf
      <;>
      linarith
    rw [h₂₁]
  
  have h₃ : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = (12 * x ^ 4 * 35) / (42 * x ^ 4) := by
    rw [h₁]
    rw [h₂]
    <;> field_simp [h₀]
    <;> ring_nf
    <;> field_simp [h₀]
    <;> ring_nf
    <;> field_simp [h₀]
    <;> linarith
  
  have h₄ : (12 * x ^ 4 * 35) / (42 * x ^ 4) = 10 := by
    have h₄₁ : x ^ 4 ≠ 0 := by
      exact pow_ne_zero 4 h₀
    have h₄₂ : (12 * x ^ 4 * 35) / (42 * x ^ 4) = 10 := by
      have h₄₃ : (12 * x ^ 4 * 35) / (42 * x ^ 4) = (12 * 35 : ℝ) / 42 := by
        field_simp [h₄₁]
        <;> ring_nf
        <;> field_simp [h₄₁]
        <;> ring_nf
      rw [h₄₃]
      norm_num
    rw [h₄₂]
  
  have h₅ : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
    rw [h₃]
    rw [h₄]
  
  rw [h₅]