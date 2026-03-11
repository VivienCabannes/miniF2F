import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p12
  (a m c : ℕ)
  (h₀ : a + m + c = 12) :
  a*m*c + a*m + m*c + a*c ≤ 112 := by
  have h₁ : a ≤ 12 := by
    omega
  
  have h₂ : m ≤ 12 := by
    omega
  
  have h₃ : c ≤ 12 := by
    omega
  
  have h₄ : a * m * c + a * m + m * c + a * c ≤ 112 := by
    have h₅ : a ≤ 12 := by omega
    have h₆ : m ≤ 12 := by omega
    have h₇ : c ≤ 12 := by omega
    -- We use interval_cases to systematically check all possible values of a, m, and c
    interval_cases a <;> interval_cases m <;> interval_cases c <;> norm_num at h₀ ⊢ <;>
      (try omega) <;> (try nlinarith) <;> (try ring_nf at h₀ ⊢ <;> omega)
    <;>
      (try norm_num at h₀ ⊢ <;> nlinarith)
    <;>
      (try ring_nf at h₀ ⊢ <;> omega)
  
  exact h₄