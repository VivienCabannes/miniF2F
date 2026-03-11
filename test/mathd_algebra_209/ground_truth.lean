import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_209
  (σ : Equiv ℝ ℝ)
  (h₀ : σ.2 2 = 10)
  (h₁ : σ.2 10 = 1)
  (h₂ : σ.2 1 = 2) :
  σ.1 (σ.1 10) = 1 := by
  have h₃ : σ.1 1 = 10 := by
    have h₃₁ : σ.1 1 = 10 := by
      have h₃₂ : σ.1 (σ.2 10) = 10 := by
        apply Equiv.apply_symm_apply
      rw [h₁] at h₃₂
      norm_num at h₃₂ ⊢
      <;> linarith
    exact h₃₁
  
  have h₄ : σ.1 2 = 1 := by
    have h₄₁ : σ.1 (σ.2 1) = 1 := by
      apply Equiv.apply_symm_apply
    rw [h₂] at h₄₁
    norm_num at h₄₁ ⊢
    <;> linarith
  
  have h₅ : σ.1 10 = 2 := by
    have h₅₁ : σ.1 (σ.2 2) = 2 := by
      apply Equiv.apply_symm_apply
    rw [h₀] at h₅₁
    norm_num at h₅₁ ⊢
    <;> linarith
  
  have h₆ : σ.1 (σ.1 10) = 1 := by
    rw [h₅]
    rw [h₄]
    <;> norm_num
  
  exact h₆