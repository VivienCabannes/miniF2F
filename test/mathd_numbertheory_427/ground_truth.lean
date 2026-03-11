import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_427
  (a : ℕ)
  (h₀ : a = (∑ k ∈ (Nat.divisors 500), k)) :
  ∑ k ∈ Finset.filter (λ x => Nat.Prime x) (Nat.divisors a), k = 25 := by
  have h₁ : a = 1092 := by
    rw [h₀]
    rw [show (∑ k in Nat.divisors 500, k) = 1092 by
      rw [show (500 : ℕ) = 2 ^ 2 * 5 ^ 3 by norm_num]
      rw [Nat.divisors_mul, Nat.divisors_prime_pow (by decide : Nat.Prime 2),
        Nat.divisors_prime_pow (by decide : Nat.Prime 5)]
      <;> rfl
    ]
    <;> rfl
  
  have h₂ : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
    rw [h₁]
    -- We need to sum all the prime divisors of 1092.
    -- First, find all the divisors of 1092.
    have h₃ : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors 1092), k) = 25 := by
      -- Manually verify the sum of prime divisors of 1092.
      rw [show (1092 : ℕ) = 2 ^ 2 * 3 * 7 * 13 by norm_num]
      -- Use the divisors of 1092 to find the sum of primes.
      rw [Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul] <;>
      -- Use the fact that the divisors of 1092 are [1, 2, 3, 4, 6, 7, 12, 13, 14, 21, 26, 28, 39, 42, 52, 78, 84, 91, 156, 182, 273, 364, 546, 1092]
      norm_num [Nat.divisors_prime_pow, Finset.sum_filter, Finset.sum_range_succ, Nat.divisors] <;>
      rfl
    -- The sum of the primes is 25.
    exact h₃
  
  exact h₂