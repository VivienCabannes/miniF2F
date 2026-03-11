import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_35 (S : Finset ℕ) (h₀ : ∀ n : ℕ, n ∈ S ↔ n ∣ Nat.sqrt 196) :
    (∑ k ∈ S, k) = 24 := by
  -- We know that the divisors of the square root of 196 are 1, 2, 4, 7, 14, and 28.
  -- We need to sum these divisors and show that the sum equals 24.
  simpa [Nat.sqrt_eq_zero, Nat.div_eq_of_eq_mul_left] using h₀ 0
  <;> decide
  <;> simp_all [Finset.sum_eq_zero]
  <;> decide