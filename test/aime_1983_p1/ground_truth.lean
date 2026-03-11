import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx : (x : ℝ) > 1 := by
    norm_cast
    <;> linarith [ht.1, ht.2.1, ht.2.2]

  have hy : (y : ℝ) > 1 := by
    norm_cast
    <;> linarith [ht.1, ht.2.1, ht.2.2]

  have hz : (z : ℝ) > 1 := by
    norm_cast
    <;> linarith [ht.1, ht.2.1, ht.2.2]

  have hxyz : (x : ℝ) * y * z > 1 := by
    have h₁ : (x : ℝ) > 1 := hx
    have h₂ : (y : ℝ) > 1 := hy
    have h₃ : (z : ℝ) > 1 := hz
    have h₄ : (x : ℝ) * y > 1 := by
      nlinarith
    nlinarith

  have hlogx : Real.log (x : ℝ) > 0 := by
    apply Real.log_pos
    <;> simpa using hx

  have hlogy : Real.log (y : ℝ) > 0 := by
    apply Real.log_pos
    <;> simpa using hy

  have hlogz : Real.log (z : ℝ) > 0 := by
    apply Real.log_pos
    <;> simpa using hz

  have hlogxyz : Real.log ((x : ℝ) * y * z) > 0 := by
    have h₁ : Real.log ((x : ℝ) * y * z) = Real.log ((x : ℝ) * y) + Real.log (z : ℝ) := by
      have h₂ : (x : ℝ) * y > 0 := by positivity
      have h₃ : (z : ℝ) > 0 := by positivity
      have h₄ : Real.log ((x : ℝ) * y * z) = Real.log ((x : ℝ) * y) + Real.log (z : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
        <;> rw [Real.log_mul (by positivity) (by positivity)]
        <;> ring
      rw [h₄]
    rw [h₁]
    have h₂ : Real.log ((x : ℝ) * y) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
      have h₃ : 0 < (x : ℝ) := by positivity
      have h₄ : 0 < (y : ℝ) := by positivity
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₂]
    have h₃ : Real.log (x : ℝ) > 0 := hlogx
    have h₄ : Real.log (y : ℝ) > 0 := hlogy
    have h₅ : Real.log (z : ℝ) > 0 := hlogz
    nlinarith

  have hlogw_pos : Real.log (w : ℝ) > 0 := by
    have h₃ : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by simpa using h0
    have h₄ : Real.log (x : ℝ) > 0 := hlogx
    have h₅ : Real.log (w : ℝ) > 0 := by
      by_contra h
      have h₆ : Real.log (w : ℝ) ≤ 0 := by linarith
      have h₇ : Real.log (w : ℝ) / Real.log (x : ℝ) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg h₆ (by linarith)
      linarith
    exact h₅

  have hlogw_eq : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    have h₃ : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by simpa using h0
    have h₄ : Real.log (x : ℝ) ≠ 0 := by linarith
    have h₅ : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
      field_simp [h₄] at h₃ ⊢
      <;> linarith
    exact h₅

  have hlogw_eq' : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    have h₃ : Real.log (w : ℝ) / Real.log (y : ℝ) = 40 := by simpa using h1
    have h₄ : Real.log (y : ℝ) ≠ 0 := by linarith
    have h₅ : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
      field_simp [h₄] at h₃ ⊢
      <;> linarith
    exact h₅

  have hlogxy : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := by
    have h₁ : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := hlogw_eq
    have h₂ : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := hlogw_eq'
    have h₃ : 24 * Real.log (x : ℝ) = 40 * Real.log (y : ℝ) := by linarith
    have h₄ : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := by
      ring_nf at h₃ ⊢
      <;> linarith
    exact h₄

  have hlogxyz_eq : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    have h₃ : Real.log (w : ℝ) / Real.log ((x : ℝ) * y * z) = 12 := by simpa using h2
    have h₄ : Real.log ((x : ℝ) * y * z) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
      have h₅ : Real.log ((x : ℝ) * y * z) = Real.log ((x : ℝ) * y) + Real.log (z : ℝ) := by
        have h₆ : 0 < (x : ℝ) * y := by positivity
        have h₇ : 0 < (z : ℝ) := by positivity
        have h₈ : Real.log ((x : ℝ) * y * z) = Real.log ((x : ℝ) * y) + Real.log (z : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        rw [h₈]
      rw [h₅]
      have h₉ : Real.log ((x : ℝ) * y) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
        have h₁₀ : 0 < (x : ℝ) := by positivity
        have h₁₁ : 0 < (y : ℝ) := by positivity
        have h₁₂ : Real.log ((x : ℝ) * y) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        rw [h₁₂]
      rw [h₉]
      <;> ring
    rw [h₄] at h₃
    have h₅ : Real.log (w : ℝ) / (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) = 12 := by simpa using h₃
    have h₆ : Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) ≠ 0 := by
      by_contra h
      rw [h] at h₅
      norm_num at h₅
      <;> linarith [hlogx, hlogy, hlogz]
    field_simp [h₆] at h₅ ⊢
    <;> nlinarith [hlogx, hlogy, hlogz, hlogw_pos, hlogw_eq, hlogw_eq', hlogxy]

  have hlogx_rel : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := by
    have h₃ : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := hlogw_eq
    have h₄ : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := hlogxyz_eq
    have h₅ : 24 * Real.log (x : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by linarith
    have h₆ : 2 * Real.log (x : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by linarith
    have h₇ : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := by linarith
    exact h₇

  have hlogz_rel : Real.log (z : ℝ) = (2 : ℝ) / 5 * Real.log (x : ℝ) := by
    have h₃ : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := hlogxy
    have h₄ : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := hlogx_rel
    have h₅ : Real.log (y : ℝ) = (3 : ℝ) / 5 * Real.log (x : ℝ) := by
      have h₅₁ : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := hlogxy
      have h₅₂ : Real.log (y : ℝ) = (3 : ℝ) / 5 * Real.log (x : ℝ) := by
        apply mul_left_cancel₀ (show (5 : ℝ) ≠ 0 by norm_num)
        nlinarith
      exact h₅₂
    have h₆ : Real.log (z : ℝ) = (2 : ℝ) / 5 * Real.log (x : ℝ) := by
      have h₆₁ : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := hlogx_rel
      rw [h₅] at h₆₁
      ring_nf at h₆₁ ⊢
      <;> nlinarith
    exact h₆

  have hgoal : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    have h₃ : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := hlogw_eq
    have h₄ : Real.log (z : ℝ) = (2 : ℝ) / 5 * Real.log (x : ℝ) := hlogz_rel
    rw [h₃, h₄]
    have h₅ : Real.log (x : ℝ) ≠ 0 := by linarith [hlogx]
    field_simp [h₅]
    <;> ring_nf
    <;> field_simp [h₅]
    <;> nlinarith [hlogx, hlogy, hlogz]

  simpa using hgoal