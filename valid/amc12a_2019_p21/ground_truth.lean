import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2019_p21 (z : ℂ) (h₀ : z = (1 + Complex.I) / Real.sqrt 2) :
  ((∑ k ∈ Finset.Icc 1 12, z ^ k ^ 2) * (∑ k ∈ Finset.Icc 1 12, 1 / z ^ k ^ 2)) = 36 := by
  have h₁ : z ^ 8 = 1 := by
    rw [h₀]
    field_simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> norm_num <;> ring_nf <;> norm_num <;> simp [Complex.ext_iff, Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> norm_num <;> ring_nf <;> norm_num
    <;> simp [Complex.ext_iff, Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> simp [Complex.ext_iff, Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> simp [Complex.ext_iff, Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> simp [Complex.ext_iff, Complex.I_mul_I, mul_comm, mul_assoc, mul_left_comm]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
  
  have h₂ : (∑ k : ℤ in Finset.Icc 1 12, z ^ k ^ 2) = 6 * z + 3 * z ^ 4 + 3 := by
    have h₂ : z = (1 + Complex.I) / Real.sqrt 2 := h₀
    have h₃ : z ^ 8 = 1 := h₁
    have h₄ : ∑ k in Finset.Icc 1 12, z ^ k ^ 2 = 6 * z + 3 * z ^ 4 + 3 := by
      have h₅ : z ^ 2 = z ^ 2 := rfl
      have h₆ : z ^ 4 = z ^ 4 := rfl
      have h₇ : z ^ 6 = z ^ 6 := rfl
      have h₈ : z ^ 8 = z ^ 8 := rfl
      simp_all [Finset.sum_Icc_succ_top, Finset.sum_range_succ, Complex.ext_iff, pow_succ, mul_add, mul_comm, mul_left_comm]
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> simp_all [Complex.ext_iff, pow_succ, mul_add, mul_comm, mul_left_comm]
      <;> norm_num
      <;> ring_nf
      <;> norm_num
    exact h₄
  have h₃ : (∑ k : ℤ in Finset.Icc 1 12, 1 / z ^ k ^ 2) = 6 * z ^ 7 + 3 * z ^ 4 + 3 := by
    simp_all [Complex.ext_iff, Complex.normSq, Complex.I_sq, pow_succ, mul_assoc, mul_comm,
      mul_left_comm]
    <;> field_simp [Complex.normSq, Complex.I_sq, pow_succ, mul_assoc, mul_comm, mul_left_comm]
    <;> ring
    <;> norm_num
    <;> simp_all [Complex.ext_iff, Complex.normSq, Complex.I_sq, pow_succ, mul_assoc, mul_comm,
      mul_left_comm]
    <;> field_simp [Complex.normSq, Complex.I_sq, pow_succ, mul_assoc, mul_comm, mul_left_comm]
    <;> ring
    <;> norm_num
    <;> simp_all [Complex.ext_iff, Complex.normSq, Complex.I_sq, pow_succ, mul_assoc, mul_comm,
      mul_left_comm]
    <;> field_simp [Complex.normSq, Complex.I_sq, pow_succ, mul_assoc, mul_comm, mul_left_comm]
    <;> ring
    <;> norm_num
  have h₄ : (6 * z + 3 * z ^ 4 + 3) * (6 * z ^ 7 + 3 * z ^ 4 + 3) = 36 := by
    have h₄ : z = (1 + Complex.I) / Real.sqrt 2 := h₀
    have h₅ : z ^ 8 = 1 := h₁
    have h₆ : (∑ k : ℤ in Finset.Icc 1 12, z ^ k ^ 2) = 6 * z + 3 * z ^ 4 + 3 := h₂
    have h₇ : (∑ k : ℤ in Finset.Icc 1 12, 1 / z ^ k ^ 2) = 6 * z ^ 7 + 3 * z ^ 4 + 3 := h₃
    subst_vars
    field_simp [Complex.ext_iff, pow_succ, Finset.sum_range_succ, Complex.I_sq, mul_comm, mul_assoc, mul_left_comm] at h₅ h₆ h₇ ⊢
    <;> ring_nf at h₅ h₆ h₇ ⊢
    <;> simp_all [Complex.ext_iff, pow_succ, Finset.sum_range_succ, Complex.I_sq, mul_comm, mul_assoc, mul_left_comm]
    <;> nlinarith [sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im), sq_nonneg (z.re + z.im - 1), sq_nonneg (z.re - z.im - 1), sq_nonneg (z.re + z.im - 2), sq_nonneg (z.re - z.im - 2)]
  have h₅ : ((∑ k : ℤ in Finset.Icc 1 12, z ^ k ^ 2) * (∑ k : ℤ in Finset.Icc 1 12, 1 / z ^ k ^ 2)) = 36 := by
    rw [h₂, h₃]
    <;> simp_all
    <;> linarith
    <;> ring
    <;> norm_num
    <;> linarith
  
  rw [h₅]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]
  <;> ring_nf at *
  <;> simp_all [Complex.ext_iff, Finset.sum_apply, mul_comm]