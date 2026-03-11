import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_392
  (n : ℕ)
  (h₀ : Even n)
  (h₁ : ((n:ℤ) - 2)^2 + (n:ℤ)^2 + ((n:ℤ) + 2)^2 = 12296) :
  ((n - 2) * n * (n + 2)) / 8 = 32736 := by
  have h₂ : (n : ℤ) ^ 2 = 4096 := by
    have h₂₁ : 3 * (n : ℤ) ^ 2 + 8 = 12296 := by
      have h₂₂ : (↑n - 2 : ℤ) ^ 2 + (↑n : ℤ) ^ 2 + (↑n + 2 : ℤ) ^ 2 = 12296 := by simpa using h₁
      ring_nf at h₂₂ ⊢
      <;> nlinarith
    have h₂₂ : (n : ℤ) ^ 2 = 4096 := by
      have h₂₃ : 3 * (n : ℤ) ^ 2 = 12288 := by linarith
      have h₂₄ : (n : ℤ) ^ 2 = 4096 := by linarith
      exact h₂₄
    exact h₂₂
  
  have h₃ : n = 64 := by
    have h₃₁ : n ≤ 64 := by
      by_contra h
      have h₃₂ : n ≥ 65 := by
        omega
      have h₃₃ : (n : ℤ) ^ 2 > 4096 := by
        have h₃₄ : (n : ℤ) ≥ 65 := by
          exact_mod_cast h₃₂
        nlinarith
      linarith
    interval_cases n <;> norm_num at h₂ ⊢
    <;>
    (try omega) <;>
    (try norm_num [Int.ofNat_eq_coe, Nat.even_iff, Nat.odd_iff] at h₀ h₁ h₂ ⊢) <;>
    (try ring_nf at h₁ h₂ ⊢) <;>
    (try linarith)
    <;>
    (try omega)
  
  have h₄ : (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
    rw [h₃]
    norm_num
    <;>
    (try ring_nf at h₁ ⊢) <;>
    (try norm_num at h₁ ⊢) <;>
    (try linarith)
    <;>
    (try omega)
  
  exact h₄