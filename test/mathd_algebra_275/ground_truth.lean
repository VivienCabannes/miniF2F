import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_275
  (x : ℝ)
  (h : ((11:ℝ)^(1 / 4))^(3 * x - 3) = 1 / 5) :
  ((11:ℝ)^(1 / 4))^(6 * x + 2) = 121 / 25 := by
  have h₁ : (11 : ℝ) ^ (1 / 4 : ℕ) = 1 := by
    norm_num
    <;>
    simp [Nat.div_eq_of_lt]
    <;>
    norm_num
    <;>
    ring_nf
    <;>
    norm_num
  
  have h₂ : ((11 : ℝ) ^ (1 / 4 : ℕ)) ^ (3 * x - 3) = 1 := by
    rw [h₁]
    <;>
    simp [Real.one_rpow]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h₃ : False := by
    have h₄ : (1 : ℝ) = 1 / 5 := by
      linarith
    norm_num at h₄
    <;> linarith
  
  have h₄ : ((11 : ℝ) ^ (1 / 4)) ^ (6 * x + 2) = 121 / 25 := by
    exfalso
    exact h₃
  
  exact h₄