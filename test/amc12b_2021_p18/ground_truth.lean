import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p18
  (z : ℂ)
  (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z^2 + 1) + 31) :
  z + 6 / z = -2 := by
  have h₁ : z.re = -1 := by
    have h₁₁ : Complex.normSq z = z.re * z.re + z.im * z.im := by
      simp [Complex.normSq_apply]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [sq_nonneg (z.re + z.im), sq_nonneg (z.re - z.im)]
    have h₁₂ : Complex.normSq (z + 2) = (z.re + 2) * (z.re + 2) + z.im * z.im := by
      simp [Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [sq_nonneg (z.re + z.im), sq_nonneg (z.re - z.im)]
    have h₁₃ : Complex.normSq (z ^ 2 + 1) = (z.re * z.re - z.im * z.im + 1) * (z.re * z.re - z.im * z.im + 1) + (2 * z.re * z.im) * (2 * z.re * z.im) := by
      simp [Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [sq_nonneg (z.re + z.im), sq_nonneg (z.re - z.im)]
    rw [h₁₁, h₁₂, h₁₃] at h₀
    have h₁₄ : z.re * z.re + z.im * z.im = (z.re * z.re + z.im * z.im) := by ring
    have h₁₅ : 12 * (z.re * z.re + z.im * z.im) = 2 * ((z.re + 2) * (z.re + 2) + z.im * z.im) + ((z.re * z.re - z.im * z.im + 1) * (z.re * z.re - z.im * z.im + 1) + (2 * z.re * z.im) * (2 * z.re * z.im)) + 31 := by
      ring_nf at h₀ ⊢
      <;> nlinarith
    have h₁₆ : (z.re + 1) = 0 := by
      nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im), sq_nonneg (z.re - 1),
        sq_nonneg (z.re * z.re + z.im * z.im - 6),
        sq_nonneg (z.re * z.re + z.im * z.im - 2 * z.re),
        sq_nonneg (z.re * z.re + z.im * z.im + 2 * z.re)]
    nlinarith
  
  have h₂ : z.re * z.re + z.im * z.im = 6 := by
    have h₂₁ : Complex.normSq z = z.re * z.re + z.im * z.im := by
      simp [Complex.normSq_apply]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [sq_nonneg (z.re + z.im), sq_nonneg (z.re - z.im)]
    have h₂₂ : Complex.normSq (z + 2) = (z.re + 2) * (z.re + 2) + z.im * z.im := by
      simp [Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [sq_nonneg (z.re + z.im), sq_nonneg (z.re - z.im)]
    have h₂₃ : Complex.normSq (z ^ 2 + 1) = (z.re * z.re - z.im * z.im + 1) * (z.re * z.re - z.im * z.im + 1) + (2 * z.re * z.im) * (2 * z.re * z.im) := by
      simp [Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> nlinarith [sq_nonneg (z.re + z.im), sq_nonneg (z.re - z.im)]
    rw [h₂₁, h₂₂, h₂₃] at h₀
    have h₂₄ : z.re * z.re + z.im * z.im = (z.re * z.re + z.im * z.im) := by ring
    have h₂₅ : 12 * (z.re * z.re + z.im * z.im) = 2 * ((z.re + 2) * (z.re + 2) + z.im * z.im) + ((z.re * z.re - z.im * z.im + 1) * (z.re * z.re - z.im * z.im + 1) + (2 * z.re * z.im) * (2 * z.re * z.im)) + 31 := by
      ring_nf at h₀ ⊢
      <;> nlinarith
    nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im), sq_nonneg (z.re - 1),
      sq_nonneg (z.re * z.re + z.im * z.im - 6),
      sq_nonneg (z.re * z.re + z.im * z.im - 2 * z.re),
      sq_nonneg (z.re * z.re + z.im * z.im + 2 * z.re)]
  
  have h₃ : z ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num [Complex.normSq, Complex.ext_iff, pow_two] at h₀
    <;>
    (try norm_num at h₀) <;>
    (try nlinarith)
    <;>
    (try simp_all [Complex.ext_iff, pow_two])
    <;>
    (try nlinarith)
  
  have h₄ : z + 6 / z = -2 := by
    have h₄₁ : z.im = Real.sqrt 5 ∨ z.im = -Real.sqrt 5 := by
      have h₄₂ : z.im * z.im = 5 := by
        nlinarith
      have h₄₃ : z.im = Real.sqrt 5 ∨ z.im = -Real.sqrt 5 := by
        apply or_iff_not_imp_left.mpr
        intro h₄₄
        apply eq_of_sub_eq_zero
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₄₄)
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      exact h₄₃
    have h₄₅ : z + 6 / z = -2 := by
      cases h₄₁ with
      | inl h₄₁ =>
        have h₄₆ : z.im = Real.sqrt 5 := h₄₁
        have h₄₇ : z.re = -1 := h₁
        have h₄₈ : z.re * z.re + z.im * z.im = 6 := h₂
        have h₄₉ : z ≠ 0 := h₃
        -- Calculate z + 6 / z using the given values
        have h₅₀ : z + 6 / z = -2 := by
          -- Compute z + 6 / z and check it equals -2
          field_simp [Complex.ext_iff, Complex.normSq, pow_two, h₄₉, Complex.ext_iff, Complex.normSq, pow_two]
          <;> simp_all [Complex.ext_iff, Complex.normSq, pow_two]
          <;> ring_nf at *
          <;> norm_num at *
          <;>
          (try
            {
              nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            })
          <;>
          (try
            {
              constructor <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            })
          <;>
          (try
            {
              nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            })
        exact h₅₀
      | inr h₄₁ =>
        have h₄₆ : z.im = -Real.sqrt 5 := h₄₁
        have h₄₇ : z.re = -1 := h₁
        have h₄₈ : z.re * z.re + z.im * z.im = 6 := h₂
        have h₄₉ : z ≠ 0 := h₃
        -- Calculate z + 6 / z using the given values
        have h₅₀ : z + 6 / z = -2 := by
          -- Compute z + 6 / z and check it equals -2
          field_simp [Complex.ext_iff, Complex.normSq, pow_two, h₄₉, Complex.ext_iff, Complex.normSq, pow_two]
          <;> simp_all [Complex.ext_iff, Complex.normSq, pow_two]
          <;> ring_nf at *
          <;> norm_num at *
          <;>
          (try
            {
              nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            })
          <;>
          (try
            {
              constructor <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            })
          <;>
          (try
            {
              nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            })
        exact h₅₀
    exact h₄₅
  
  exact h₄