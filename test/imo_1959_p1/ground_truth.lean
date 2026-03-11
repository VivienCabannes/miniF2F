import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1959_p1
  (n : ℕ)
  (h₀ : 0 < n) :
  Nat.gcd (21*n + 4) (14*n + 3) = 1 := by
  have h₁ : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
    have h₁₀ : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
      rw [show 21 * n + 4 = 1 * (14 * n + 3) + (7 * n + 1) by
        ring_nf
        <;> omega]
      -- Apply the Euclidean algorithm step: 21n + 4 = 1 * (14n + 3) + (7n + 1)
      rw [Nat.gcd_comm]
      <;> simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right, Nat.gcd_assoc, Nat.gcd_assoc]
      <;> ring_nf at *
      <;> omega
    exact h₁₀
    <;> simp_all
  
  have h₂ : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
    have h₂₁ : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
      have h₂₁₁ : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
        rw [show 14 * n + 3 = 2 * (7 * n + 1) + 1 by
          ring_nf
          <;> omega]
        <;> simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right, Nat.gcd_assoc]
        <;> ring_nf at *
        <;> omega
      exact h₂₁₁
    exact h₂₁
  
  have h₃ : Nat.gcd (7 * n + 1) 1 = 1 := by
    have h₃₁ : Nat.gcd (7 * n + 1) 1 = 1 := by
      simp [Nat.gcd_eq_right]
    exact h₃₁
  
  have h₄ : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    rw [h₁]
    rw [h₂]
    rw [h₃]
    <;> simp_all [Nat.gcd_eq_right]
    <;> ring_nf at *
    <;> omega
  
  exact h₄