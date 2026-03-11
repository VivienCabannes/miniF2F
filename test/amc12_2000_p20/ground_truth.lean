import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p20
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + 1/y = 4)
  (h₂ : y + 1/z = 1)
  (h₃ : z + 1/x = 7/3) :
  x*y*z = 1 := by
  have h₄ : x * y + 1 = 4 * y := by
    have h₄₁ : y ≠ 0 := by linarith
    have h₄₂ : x + 1 / y = 4 := h₁
    field_simp at h₄₂ ⊢
    nlinarith [h₀.1, h₀.2.1, h₀.2.2]
  
  have h₅ : y * z + 1 = z := by
    have h₅₁ : z ≠ 0 := by linarith
    have h₅₂ : y + 1 / z = 1 := h₂
    field_simp at h₅₂ ⊢
    nlinarith [h₀.1, h₀.2.1, h₀.2.2]
  
  have h₆ : x * z + 1 = 7 / 3 * x := by
    have h₆₁ : x ≠ 0 := by linarith
    have h₆₂ : z + 1 / x = 7 / 3 := h₃
    field_simp at h₆₂ ⊢
    nlinarith [h₀.1, h₀.2.1, h₀.2.2]
  
  have h₇ : y < 1 := by
    by_contra h
    have h₇₁ : y ≥ 1 := by linarith
    have h₇₂ : z > 0 := by linarith
    have h₇₃ : y * z + 1 = z := h₅
    have h₇₄ : y * z ≥ z := by nlinarith
    nlinarith
  
  have h₈ : z = 1 / (1 - y) := by
    have h₈₁ : y < 1 := h₇
    have h₈₂ : y * z + 1 = z := h₅
    have h₈₃ : 1 - y > 0 := by linarith
    have h₈₄ : z = 1 / (1 - y) := by
      have h₈₅ : z * (1 - y) = 1 := by
        have h₈₅₁ : y * z + 1 = z := h₅
        nlinarith
      have h₈₅₂ : z = 1 / (1 - y) := by
        have h₈₅₃ : 1 - y ≠ 0 := by linarith
        field_simp at h₈₅ ⊢
        nlinarith
      exact h₈₅₂
    exact h₈₄
  
  have h₉ : y = 1 / (4 - x) := by
    have h₉₁ : x * y + 1 = 4 * y := h₄
    have h₉₂ : y > 0 := by linarith
    have h₉₃ : 4 - x > 0 := by
      by_contra h
      have h₉₄ : x ≥ 4 := by linarith
      have h₉₅ : x * y + 1 = 4 * y := h₄
      have h₉₆ : x * y ≥ 4 * y := by nlinarith
      nlinarith
    have h₉₄ : y = 1 / (4 - x) := by
      have h₉₅ : x * y + 1 = 4 * y := h₄
      have h₉₆ : y * (4 - x) = 1 := by
        nlinarith
      have h₉₇ : y = 1 / (4 - x) := by
        have h₉₈ : 4 - x ≠ 0 := by linarith
        field_simp at h₉₆ ⊢
        nlinarith
      exact h₉₇
    exact h₉₄
  
  have h₁₀ : x < 4 := by
    by_contra h
    have h₁₀₁ : x ≥ 4 := by linarith
    have h₁₀₂ : y > 0 := by linarith
    have h₁₀₃ : x * y + 1 = 4 * y := h₄
    have h₁₀₄ : x * y ≥ 4 * y := by nlinarith
    nlinarith
  
  have h₁₁ : z = (4 - x) / (3 - x) := by
    have h₁₁₁ : z = 1 / (1 - y) := h₈
    have h₁₁₂ : y = 1 / (4 - x) := h₉
    have h₁₁₃ : z = (4 - x) / (3 - x) := by
      rw [h₁₁₁, h₁₁₂]
      have h₁₁₄ : 1 - (1 / (4 - x)) ≠ 0 := by
        have h₁₁₅ : 4 - x > 0 := by linarith
        have h₁₁₆ : 1 - (1 / (4 - x)) > 0 := by
          have h₁₁₇ : 0 < 4 - x := by linarith
          have h₁₁₈ : 0 < (4 - x : ℝ) := by exact_mod_cast h₁₁₇
          field_simp [h₁₁₈.ne']
          rw [← sub_pos]
          field_simp [h₁₁₈.ne']
          <;> nlinarith
        linarith
      have h₁₁₅ : 3 - x ≠ 0 := by
        have h₁₁₆ : x < 4 := h₁₀
        have h₁₁₇ : x > 0 := by linarith
        by_contra h₁₁₈
        have h₁₁₉ : 3 - x = 0 := by linarith
        have h₁₂₀ : x = 3 := by linarith
        have h₁₂₁ : x * z + 1 = 7 / 3 * x := h₆
        have h₁₂₂ : z = (4 - x) / (3 - x) := by
          rw [h₁₁₈]
          <;> field_simp [h₁₁₈] at *
          <;> nlinarith
        rw [h₁₂₀] at h₁₂₁ h₁₂₂
        <;> norm_num at h₁₂₁ h₁₂₂ ⊢ <;>
          (try norm_num) <;> (try nlinarith) <;> (try linarith)
      field_simp [h₁₁₄, h₁₁₅]
      <;>
      (try ring_nf at * <;> nlinarith) <;>
      (try field_simp [h₁₁₄, h₁₁₅] at * <;> nlinarith)
    exact h₁₁₃
  
  have h₁₂ : 4 * x ^ 2 - 12 * x + 9 = 0 := by
    have h₁₂₁ : z = (4 - x) / (3 - x) := h₁₁
    have h₁₂₂ : x * z + 1 = 7 / 3 * x := h₆
    rw [h₁₂₁] at h₁₂₂
    have h₁₂₃ : x < 4 := h₁₀
    have h₁₂₄ : x > 0 := by linarith
    have h₁₂₅ : 3 - x ≠ 0 := by
      by_contra h
      have h₁₂₆ : 3 - x = 0 := by linarith
      have h₁₂₇ : x = 3 := by linarith
      rw [h₁₂₇] at h₁₂₂
      norm_num at h₁₂₂ ⊢
      <;> nlinarith
    field_simp [h₁₂₅] at h₁₂₂
    <;> ring_nf at h₁₂₂ ⊢
    <;> nlinarith [sq_nonneg (x - 3 / 2)]
  
  have h₁₃ : x = 3 / 2 := by
    have h₁₃₁ : 4 * x ^ 2 - 12 * x + 9 = 0 := h₁₂
    have h₁₃₂ : x = 3 / 2 := by
      nlinarith [sq_nonneg (x - 3 / 2)]
    exact h₁₃₂
  
  have h₁₄ : y = 2 / 5 := by
    have h₁₄₁ : y = 1 / (4 - x) := h₉
    rw [h₁₄₁]
    rw [h₁₃]
    <;> norm_num
    <;>
    (try norm_num at * <;> nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf at * <;> nlinarith)
  
  have h₁₅ : z = 5 / 3 := by
    have h₁₅₁ : z = (4 - x) / (3 - x) := h₁₁
    rw [h₁₅₁]
    rw [h₁₃]
    <;> norm_num
    <;>
    (try norm_num at * <;> nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf at * <;> nlinarith)
  
  have h₁₆ : x * y * z = 1 := by
    rw [h₁₃, h₁₄, h₁₅]
    <;> norm_num
    <;>
    (try ring_nf at * <;> nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf at * <;> nlinarith)
    <;>
    (try linarith)
  
  exact h₁₆