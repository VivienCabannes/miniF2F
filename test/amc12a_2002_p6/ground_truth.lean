import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2002_p6
  (n : ℕ)
  (h₀ : 0 < n) :
  ∃ m, (m > n ∧ ∃ p, m * p ≤ m + p) := by
  have h₁ : ∃ (m : ℕ), m > n ∧ ∃ (p : ℕ), m * p ≤ m + p := by
    use n + 1
    constructor
    · -- Prove that n + 1 > n
      omega
    · -- Prove that there exists a p such that (n + 1) * p ≤ (n + 1) + p
      use 0
      <;> simp [Nat.mul_zero, Nat.add_zero]
      <;> omega
  -- The main goal follows directly from h₁
  exact h₁