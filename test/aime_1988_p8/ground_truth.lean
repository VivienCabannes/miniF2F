import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 := by
  have h₃ : f 2 2 = 2 := by
    have h₃₁ : f 2 2 = 2 := by
      have h₃₂ : f 2 2 = (2 : ℝ) := by
        have h₃₃ : (0 : ℕ) < 2 := by decide
        have h₃₄ : f 2 2 = (2 : ℝ) := by
          simpa using h₀ 2 (by decide)
        exact h₃₄
      exact_mod_cast h₃₂
    exact h₃₁
  
  have h₄ : f 2 4 = 4 := by
    have h₄₁ : (↑2 + ↑2 : ℝ) * f 2 2 = (2 : ℝ) * f 2 4 := by
      have h₄₂ : 0 < (2 : ℕ) ∧ 0 < (2 : ℕ) := by norm_num
      have h₄₃ := h₂ 2 2 h₄₂
      norm_num at h₄₃ ⊢
      <;> linarith
    have h₄₂ : (↑2 + ↑2 : ℝ) * f 2 2 = (2 : ℝ) * f 2 4 := by
      exact h₄₁
    have h₄₃ : f 2 2 = (2 : ℝ) := by exact_mod_cast h₃
    have h₄₄ : (↑2 + ↑2 : ℝ) * f 2 2 = (2 : ℝ) * f 2 4 := by exact h₄₂
    have h₄₅ : f 2 4 = 4 := by
      rw [h₄₃] at h₄₄
      ring_nf at h₄₄ ⊢
      <;> linarith
    exact_mod_cast h₄₅
  
  have h₅ : f 4 2 = 4 := by
    have h₅₁ : f 4 2 = f 2 4 := by
      apply h₁ 4 2
      <;> norm_num
    rw [h₅₁]
    exact_mod_cast h₄
  
  have h₆ : f 4 6 = 12 := by
    have h₆₁ : (↑4 + ↑2 : ℝ) * f 4 2 = (↑2 : ℝ) * f 4 6 := by
      have h₆₂ : 0 < (4 : ℕ) ∧ 0 < (2 : ℕ) := by norm_num
      have h₆₃ := h₂ 4 2 h₆₂
      norm_num at h₆₃ ⊢ <;> ring_nf at h₆₃ ⊢ <;>
        (try norm_num at h₆₃ ⊢) <;>
        (try linarith) <;>
        (try ring_nf at h₆₃ ⊢ <;> norm_num at h₆₃ ⊢ <;> linarith)
      <;>
      (try linarith)
    have h₆₄ : (↑4 + ↑2 : ℝ) * f 4 2 = (↑2 : ℝ) * f 4 6 := by
      exact h₆₁
    have h₆₅ : f 4 2 = (4 : ℝ) := by exact_mod_cast h₅
    have h₆₆ : (↑4 + ↑2 : ℝ) * f 4 2 = (↑2 : ℝ) * f 4 6 := by exact h₆₁
    have h₆₇ : f 4 6 = 12 := by
      rw [h₆₅] at h₆₆
      ring_nf at h₆₆ ⊢
      <;> linarith
    exact_mod_cast h₆₇
  
  have h₇ : f 4 10 = 20 := by
    have h₇₁ : (↑4 + ↑6 : ℝ) * f 4 6 = (↑6 : ℝ) * f 4 10 := by
      have h₇₂ : 0 < (4 : ℕ) ∧ 0 < (6 : ℕ) := by norm_num
      have h₇₃ := h₂ 4 6 h₇₂
      norm_num at h₇₃ ⊢ <;> ring_nf at h₇₃ ⊢ <;>
        (try norm_num at h₇₃ ⊢) <;>
        (try linarith) <;>
        (try ring_nf at h₇₃ ⊢ <;> norm_num at h₇₃ ⊢ <;> linarith)
      <;>
      (try linarith)
    have h₇₄ : (↑4 + ↑6 : ℝ) * f 4 6 = (↑6 : ℝ) * f 4 10 := by
      exact h₇₁
    have h₇₅ : f 4 6 = (12 : ℝ) := by exact_mod_cast h₆
    have h₇₆ : (↑4 + ↑6 : ℝ) * f 4 6 = (↑6 : ℝ) * f 4 10 := by exact h₇₁
    have h₇₇ : f 4 10 = 20 := by
      rw [h₇₅] at h₇₆
      ring_nf at h₇₆ ⊢
      <;> linarith
    exact_mod_cast h₇₇
  
  have h₈ : f 10 4 = 20 := by
    have h₈₁ : f 10 4 = f 4 10 := by
      apply h₁
      <;> norm_num
    rw [h₈₁]
    exact_mod_cast h₇
  
  have h₉ : f 10 14 = 70 := by
    have h₉₁ : (↑10 + ↑4 : ℝ) * f 10 4 = (↑4 : ℝ) * f 10 14 := by
      have h₉₂ : 0 < (10 : ℕ) ∧ 0 < (4 : ℕ) := by norm_num
      have h₉₃ := h₂ 10 4 h₉₂
      norm_num at h₉₃ ⊢ <;> ring_nf at h₉₃ ⊢ <;>
        (try norm_num at h₉₃ ⊢) <;>
        (try linarith) <;>
        (try ring_nf at h₉₃ ⊢ <;> norm_num at h₉₃ ⊢ <;> linarith)
      <;>
      (try linarith)
    have h₉₄ : (↑10 + ↑4 : ℝ) * f 10 4 = (↑4 : ℝ) * f 10 14 := by
      exact h₉₁
    have h₉₅ : f 10 4 = (20 : ℝ) := by exact_mod_cast h₈
    have h₉₆ : (↑10 + ↑4 : ℝ) * f 10 4 = (↑4 : ℝ) * f 10 14 := by exact h₉₁
    have h₉₇ : f 10 14 = 70 := by
      rw [h₉₅] at h₉₆
      ring_nf at h₉₆ ⊢
      <;> linarith
    exact_mod_cast h₉₇
  
  have h₁₀ : f 14 10 = 70 := by
    have h₁₀₁ : f 14 10 = f 10 14 := by
      apply h₁
      <;> norm_num
    rw [h₁₀₁]
    exact_mod_cast h₉
  
  have h₁₁ : f 14 24 = 168 := by
    have h₁₁₁ : (↑14 + ↑10 : ℝ) * f 14 10 = (↑10 : ℝ) * f 14 24 := by
      have h₁₁₂ : 0 < (14 : ℕ) ∧ 0 < (10 : ℕ) := by norm_num
      have h₁₁₃ := h₂ 14 10 h₁₁₂
      norm_num at h₁₁₃ ⊢ <;> ring_nf at h₁₁₃ ⊢ <;>
        (try norm_num at h₁₁₃ ⊢) <;>
        (try linarith) <;>
        (try ring_nf at h₁₁₃ ⊢ <;> norm_num at h₁₁₃ ⊢ <;> linarith)
      <;>
      (try linarith)
    have h₁₁₄ : (↑14 + ↑10 : ℝ) * f 14 10 = (↑10 : ℝ) * f 14 24 := by
      exact h₁₁₁
    have h₁₁₅ : f 14 10 = (70 : ℝ) := by exact_mod_cast h₁₀
    have h₁₁₆ : (↑14 + ↑10 : ℝ) * f 14 10 = (↑10 : ℝ) * f 14 24 := by exact h₁₁₁
    have h₁₁₇ : f 14 24 = 168 := by
      rw [h₁₁₅] at h₁₁₆
      ring_nf at h₁₁₆ ⊢
      <;> linarith
    exact_mod_cast h₁₁₇
  
  have h₁₂ : f 14 38 = 266 := by
    have h₁₂₁ : (↑14 + ↑24 : ℝ) * f 14 24 = (↑24 : ℝ) * f 14 38 := by
      have h₁₂₂ : 0 < (14 : ℕ) ∧ 0 < (24 : ℕ) := by norm_num
      have h₁₂₃ := h₂ 14 24 h₁₂₂
      norm_num at h₁₂₃ ⊢ <;> ring_nf at h₁₂₃ ⊢ <;>
        (try norm_num at h₁₂₃ ⊢) <;>
        (try linarith) <;>
        (try ring_nf at h₁₂₃ ⊢ <;> norm_num at h₁₂₃ ⊢ <;> linarith)
      <;>
      (try linarith)
    have h₁₂₄ : (↑14 + ↑24 : ℝ) * f 14 24 = (↑24 : ℝ) * f 14 38 := by
      exact h₁₂₁
    have h₁₂₅ : f 14 24 = (168 : ℝ) := by exact_mod_cast h₁₁
    have h₁₂₆ : (↑14 + ↑24 : ℝ) * f 14 24 = (↑24 : ℝ) * f 14 38 := by exact h₁₂₁
    have h₁₂₇ : f 14 38 = 266 := by
      rw [h₁₂₅] at h₁₂₆
      ring_nf at h₁₂₆ ⊢
      <;> linarith
    exact_mod_cast h₁₂₇
  
  have h₁₃ : f 14 52 = 364 := by
    have h₁₃₁ : (↑14 + ↑38 : ℝ) * f 14 38 = (↑38 : ℝ) * f 14 52 := by
      have h₁₃₂ : 0 < (14 : ℕ) ∧ 0 < (38 : ℕ) := by norm_num
      have h₁₃₃ := h₂ 14 38 h₁₃₂
      norm_num at h₁₃₃ ⊢ <;> ring_nf at h₁₃₃ ⊢ <;>
        (try norm_num at h₁₃₃ ⊢) <;>
        (try linarith) <;>
        (try ring_nf at h₁₃₃ ⊢ <;> norm_num at h₁₃₃ ⊢ <;> linarith)
      <;>
      (try linarith)
    have h₁₃₄ : (↑14 + ↑38 : ℝ) * f 14 38 = (↑38 : ℝ) * f 14 52 := by
      exact h₁₃₁
    have h₁₃₅ : f 14 38 = (266 : ℝ) := by exact_mod_cast h₁₂
    have h₁₃₆ : (↑14 + ↑38 : ℝ) * f 14 38 = (↑38 : ℝ) * f 14 52 := by exact h₁₃₁
    have h₁₃₇ : f 14 52 = 364 := by
      rw [h₁₃₅] at h₁₃₆
      ring_nf at h₁₃₆ ⊢
      <;> linarith
    exact_mod_cast h₁₃₇
  
  exact h₁₃