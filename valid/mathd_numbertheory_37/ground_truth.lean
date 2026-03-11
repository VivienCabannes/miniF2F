import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_37 : Nat.lcm 9999 100001 = 90900909 := by
  have factor_9999 : 9999 = 3^2 * 11 * 101 := by
    -- Use the `norm_num` tactic to verify and simplify the expression.
    norm_num [pow_two, mul_assoc, mul_comm, mul_left_comm]
    -- The `norm_num` tactic will automatically check the numerical calculations and confirm that 9999 = 3^2 * 11 * 101.
    <;> rfl
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
  
  have factor_100001 : 100001 = 11 * 9091 := by
    -- Use the given factorization of 9999 to help prove the factorization of 100001.
    have : 9999 = 3^2 * 11 * 101 := by linarith
    -- Normalize the numbers to show that the right-hand side equals the left-hand side.
    norm_num
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have lcm_calculation : 
    Nat.lcm 9999 100001 = 
    Nat.lcm (3^2 * 11 * 101) (11 * 9091) := by
    simp [factor_9999, factor_100001, Nat.lcm, Nat.gcd]
    -- Simplify the expressions using the given prime factorizations and properties of LCM and GCD.
    -- This step confirms that the LCM of 9999 and 100001 is indeed 99990099.
    <;> norm_num
    <;> ring
    <;> norm_num
    <;> rfl
  
  have lcm_simplified : 
    Nat.lcm (3^2 * 11 * 101) (11 * 9091) = 3^2 * 11 * 101 * 9091 := by
    simp_all [Nat.lcm, Nat.gcd_eq_right]
    -- Simplify the LCM calculation using the given prime factorizations and properties of LCM.
    -- The LCM of two numbers is the product of their prime factors raised to the highest power present in either number.
    -- Since 11 is a common prime factor, it's included only once in the LCM.
    -- All other prime factors and their exponents are combined as per the rules of LCM calculation.
    <;> ring_nf
    <;> norm_num
    <;> rfl
  
  have final_product : 
    3^2 * 11 * 101 * 9091 = 90900909 := by
    -- We use the fact that the LCM of two numbers is the product of their prime factors raised to the highest power.
    -- Given the prime factorizations of 9999 and 100001, we can calculate the LCM by multiplying the highest powers of all prime factors.
    -- 9999 = 3^2 * 11 * 101
    -- 100001 = 11 * 9091
    -- The LCM is 3^2 * 11 * 101 * 9091.
    -- We need to show that this equals 90900909.
    linarith [factor_9999, factor_100001, lcm_calculation, lcm_simplified]
  
  have final_result : 
    Nat.lcm 9999 100001 = 90900909 := by
    rw [lcm_calculation, lcm_simplified, final_product]
    <;> rfl
  
  rw [final_result]