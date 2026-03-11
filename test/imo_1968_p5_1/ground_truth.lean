import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1968_p5_1
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a)
  (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - (f x)^2)) :
  ∃ b > 0, ∀ x, f (x + b) = f x := by
  have h₂ : ∀ x, f x ≥ 1 / 2 := by
    intro x
    have h₂₁ : f x = 1 / 2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
      have h₂₂ := h₁ (x - a)
      ring_nf at h₂₂ ⊢
      linarith
    rw [h₂₁]
    have h₂₂ : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≥ 0 := by
      apply Real.sqrt_nonneg
    linarith
  
  have h₃ : ∀ x, f x ≤ 1 := by
    intro x
    by_contra h
    have h₄ : f x > 1 := by linarith
    have h₅ : f x = 1 / 2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
      have h₅₁ := h₁ (x - a)
      ring_nf at h₅₁ ⊢
      linarith
    rw [h₅] at h₄
    have h₆ : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ 1 / 2 := by
      have h₆₁ : f (x - a) - f (x - a) ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_nonneg (f (x - a) - 1 / 2), h₂ (x - a)]
      have h₆₂ : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ 1 / 2 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · nlinarith [h₂ (x - a)]
        · nlinarith [h₂ (x - a)]
      exact h₆₂
    linarith
  
  have h₄ : ∀ x, f (x + 2 * a) = f x := by
    intro x
    have h₄₁ : f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2) := by
      apply h₁
    have h₄₂ : f (x + 2 * a) = f ((x + a) + a) := by ring
    rw [h₄₂]
    have h₄₃ : f ((x + a) + a) = 1 / 2 + Real.sqrt (f (x + a) - f (x + a) ^ 2) := by
      have h₄₄ := h₁ (x + a)
      ring_nf at h₄₄ ⊢
      linarith
    rw [h₄₃]
    have h₄₅ : f (x + a) - f (x + a) ^ 2 = (f x - 1 / 2) ^ 2 := by
      have h₄₅₁ : f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2) := by
        apply h₁
      rw [h₄₅₁]
      have h₄₅₂ : f x - f x ^ 2 ≥ 0 := by
        nlinarith [h₂ x, h₃ x, sq_nonneg (f x - 1 / 2), Real.sqrt_nonneg (f x - f x ^ 2)]
      have h₄₅₃ : Real.sqrt (f x - f x ^ 2) ≥ 0 := Real.sqrt_nonneg (f x - f x ^ 2)
      have h₄₅₄ : Real.sqrt (f x - f x ^ 2) ^ 2 = f x - f x ^ 2 := by
        rw [Real.sq_sqrt] <;> nlinarith [h₂ x, h₃ x]
      nlinarith [h₂ x, h₃ x, sq_nonneg (f x - 1 / 2), h₄₅₄]
    have h₄₆ : Real.sqrt (f (x + a) - f (x + a) ^ 2) = f x - 1 / 2 := by
      rw [h₄₅]
      have h₄₆₁ : f x ≥ 1 / 2 := h₂ x
      have h₄₆₂ : f x ≤ 1 := h₃ x
      have h₄₆₃ : Real.sqrt ((f x - 1 / 2) ^ 2) = f x - 1 / 2 := by
        rw [Real.sqrt_sq (by nlinarith [h₂ x, h₃ x])]
      rw [h₄₆₃]
    rw [h₄₆]
    <;> ring_nf <;> nlinarith [h₂ x, h₃ x, h₂ (x + a), h₃ (x + a)]
  
  have h₅ : ∃ b > 0, ∀ x, f (x + b) = f x := by
    refine' ⟨2 * a, by linarith, _⟩
    intro x
    have h₅₁ : f (x + 2 * a) = f x := h₄ x
    have h₅₂ : f (x + 2 * a) = f x := h₄ x
    simpa [add_assoc] using h₅₁
  
  exact h₅