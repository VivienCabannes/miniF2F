import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_188
  (σ : Equiv ℝ ℝ)
  (h : σ.1 2 = σ.2 2) :
  σ.1 (σ.1 2) = 2 := by
  have h₁ : σ.1 (σ.1 2) = σ.1 (σ.2 2) := by
    rw [h]
    <;> simp [Equiv.toFun_as_coe, Equiv.invFun_as_coe]
    <;>
    aesop
  
  have h₂ : σ.1 (σ.2 2) = 2 := by
    have h₂₁ : σ.1 (σ.2 2) = 2 := by
      apply Equiv.apply_symm_apply
    exact h₂₁
  
  have h₃ : σ.1 (σ.1 2) = 2 := by
    rw [h₁]
    rw [h₂]
    <;> simp [Equiv.toFun_as_coe, Equiv.invFun_as_coe]
    <;>
    aesop
  
  apply h₃