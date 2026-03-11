import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_543 : (∑ k ∈ Nat.divisors (30 ^ 4), 1) - 2 = 123 := by
  have prime_factors_30 : 30 = 2 * 3 * 5 := by
    -- Use the `norm_num` tactic to verify the numerical equality.
    norm_num
    -- Use the `decide` tactic to conclude the proof.
    <;> decide
    <;> decide
    <;> decide
  
  have pow_30_4 : 30^4 = (2 * 3 * 5)^4 := by
    -- We start by rewriting the base 30 as its prime factors and then raise both sides to the 4th power.
    rw [prime_factors_30]
    -- Simplify both sides of the equation using the property of exponents.
    <;> simp_all [pow_succ]
    -- Normalize the numbers to confirm that both sides are equal.
    <;> norm_num
    <;> norm_num
    <;> norm_num
  
  have expanded_pow : (2 * 3 * 5)^4 = 2^4 * 3^4 * 5^4 := by
    -- Simplify the expression using the properties of exponents and the prime factorization of 30.
    simp [pow_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm, prime_factors_30, pow_30_4]
    -- Use the ring tactic to simplify the expression and verify the equality.
    <;> ring
  
  have num_divisors : (4 + 1) * (4 + 1) * (4 + 1) = 125 := by
    -- Given the prime factors of 30 and the expansion of 30^4, we can directly compute the number of divisors.
    have h : (4 + 1) * (4 + 1) * (4 + 1) = 125 := by
      -- Simplify the expression using the given prime factors and expanded form.
      simp [prime_factors_30, pow_30_4, expanded_pow]
    -- The final result is 125.
    exact h
  
  have total_divisors : ∑ k in Nat.divisors (30^4), 1 = 125 := by
    -- Simplify the expression for 30^4 using the given prime factorisation
    simp_all only [mul_assoc, mul_comm, mul_left_comm, Nat.divisors_mul]
    -- Use the calculated number of divisors and the sum of the divisors
    rfl
    <;> decide
  
  have result : (∑ k in Nat.divisors (30^4), 1) - 2 = 123 := by
    -- Using the given information about the number of divisors and the total number of divisors,
    -- we can directly compute the result by subtracting 2 from the total number of divisors.
    simpa [prime_factors_30, pow_30_4, expanded_pow, num_divisors, total_divisors] using
      total_divisors
  
  -- We use the given information to simplify the proof
  simpa [prime_factors_30, pow_30_4, expanded_pow, num_divisors, total_divisors] using result