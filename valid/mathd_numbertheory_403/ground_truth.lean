import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_403 : (∑ k ∈ Nat.properDivisors 198, k) = 270 := by
  have prime_factors : 198 = 2^1 * 3^2 * 11^1 := by
    -- Use the `norm_num` tactic to verify the numerical equality.
    -- The `show` tactic is used to provide a proof term for the equality, which `norm_num` will then verify.
    norm_num [show 2^1 * 3^2 * 11^1 = 198 by ring]
  
  have num_divisors : Fintype.card (Nat.divisors 198) = 12 := by
    -- We use the fact that the number of divisors of a number can be calculated from its prime factorization.
    rw [Nat.divisors]
    -- We calculate the number of divisors using the formula (e1 + 1)(e2 + 1)...(en + 1) where e1, e2, ..., en are the exponents in the prime factorization.
    -- For 198 = 2^1 * 3^2 * 11^1, the exponents are 1, 2, and 1 respectively.
    -- Therefore, the number of divisors is (1 + 1)(2 + 1)(1 + 1) = 2 * 3 * 2 = 12.
    rfl
  
  have all_divisors : (Nat.divisors 198) = {1, 2, 3, 6, 9, 11, 18, 22, 33, 66, 99, 198} := by
    rw [Nat.divisors]
    -- We need to show that the set of divisors of 198 is exactly the set {1, 2, 3, 6, 9, 11, 18, 22, 33, 66, 99, 198}.
    -- This can be done by showing that each element in the set is a divisor of 198 and that there are no other divisors.
    rfl
    -- The `rfl` tactic is used to confirm that the set of divisors is correctly computed by Lean4.
    -- This tactic relies on the fact that the prime factors and their exponents are correctly provided in the theorem statement.
    <;> norm_num
    -- The `norm_num` tactic is used to normalize the numbers and ensure that they are correct.
    -- This is particularly useful for checking the correctness of the prime factors and their exponents.
    <;> decide
    -- The `decide` tactic is used to confirm the divisibility of each element in the set by 198.
    -- This tactic is particularly useful for checking the correctness of the set of divisors.
    <;> simp_all
    -- The `simp_all` tactic is used to simplify the context and ensure that all elements in the set are indeed divisors of 198.
    -- This tactic is particularly useful for simplifying the context and ensuring that the set of divisors is correctly computed.
    <;> norm_num
    <;> decide
    <;> simp_all
    <;> norm_num
    <;> decide
    <;> simp_all
    <;> norm_num
    <;> decide
    <;> simp_all
    <;> norm_num
    <;> decide
  
  have proper_divisors : (Nat.properDivisors 198) = {1, 2, 3, 6, 9, 11, 18, 22, 33, 66, 99} := by
    -- Replace the divisors of 198 with the proper divisors of 198
    rw [show (Nat.divisors 198) = {1, 2, 3, 6, 9, 11, 18, 22, 33, 66, 99, 198} by
      rw [all_divisors]
    ] at num_divisors
    -- Simplify the expression to find the proper divisors of 198
    simp_all [Nat.properDivisors, Finset.filter_eq]
    -- Use decision procedure to confirm the proper divisors of 198
    <;> decide
  
  have sum_proper_divisors : (∑ k in Nat.properDivisors 198, k) = 270 := by
    rw [proper_divisors]
    -- We need to sum the elements in the set of proper divisors of 198.
    -- The proper divisors of 198 are {1, 2, 3, 6, 9, 11, 18, 22, 33, 66, 99}.
    -- We can directly compute the sum of these elements.
    norm_num
    -- This tactic will compute the sum of the elements in the set.
    <;> rfl
    -- This tactic will verify that the computed sum matches the expected result.
    <;> simp_all [Nat.divisors]
    -- This tactic will simplify the expressions and verify the sum.
    <;> decide
    -- This tactic will ensure that all steps are correct and the sum is indeed 270.
    <;> rfl
  
  -- Since the sum of the proper divisors is given as 270, we directly use this fact.
  exact sum_proper_divisors