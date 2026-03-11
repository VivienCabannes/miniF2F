import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_169 : Nat.gcd 20! 200000 = 40000 := by
  have h1 : 20! = 2^18 * 3^8 * 5^4 * 7^2 * 11 * 13 * 17 * 19 := by
    -- Use the `decide` tactic to verify the equality by computation.
    decide
    <;>
      norm_num
    <;>
      decide
    <;>
      norm_num
    <;>
      decide
    <;>
      norm_num
    <;>
      decide
    <;>
      norm_num
    <;>
      decide
    <;>
      norm_num
    <;>
      decide
    <;>
      norm_num
    <;>
      decide
  
  have h2 : 200000 = 2^6 * 5^5 := by
    -- We start by normalizing the given factorial expression and the target expression.
    norm_num [Nat.factorial, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    -- We simplify the expressions to show that 200,000 equals 2^6 * 5^5.
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have h3 : Nat.gcd (2^18) (2^6) = 2^6 := by
    -- Simplify the gcd calculation using the properties of gcd for powers of the same base.
    simp_all [Nat.gcd_eq_right, Nat.pow_le_pow_of_le_right]
    -- Verify the numerical values to confirm the gcd.
    <;> norm_num
  
  have h4 : Nat.gcd (5^4) (5^5) = 5^4 := by
    -- Simplify the gcd of 5^4 and 5^5 using the fact that the gcd of two powers of the same base is the base raised to the smaller exponent.
    simp [h3, Nat.gcd_eq_right, Nat.gcd_eq_left]
    -- Verify that the gcd of 5^4 and 5^5 is indeed 5^4.
    <;> rfl
  
  have h5 : Nat.gcd (3^8) 1 = 1 := by
    -- Simplify the gcd of 3^8 and 1 using the fact that gcd(a, 1) = 1 for any integer a.
    simp [Nat.gcd_eq_right]
    -- Verify the calculations using norm_num to ensure correctness.
    <;> norm_num
    <;> rfl
    <;> rfl
    <;> rfl
  
  have h6 : Nat.gcd (7^2) 1 = 1 := by
    -- Simplify the expression using the given hypotheses and properties of gcd.
    simp [h3, h4, h5, Nat.gcd_eq_right]
    -- Each step uses the properties of gcd to simplify the expression, leading to the final result.
    <;> simp [h3, h4, h5, Nat.gcd_eq_right]
    <;> simp [h3, h4, h5, Nat.gcd_eq_right]
    <;> simp [h3, h4, h5, Nat.gcd_eq_right]
    <;> simp [h3, h4, h5, Nat.gcd_eq_right]
  
  have h7 : Nat.gcd 11 1 = 1 := by
    -- Use the property that the gcd of any number and 1 is 1.
    simpa using h5
  
  have h8 : Nat.gcd 13 1 = 1 := by
    simp [Nat.gcd_eq_right]
    <;> aesop
  
  have h9 : Nat.gcd 17 1 = 1 := by
    -- Simplify the expression for the gcd of 17 and 1.
    simp [Nat.gcd_eq_right]
    -- Since 17 is a prime number and does not divide 1, the gcd is 1.
    <;> norm_num
    <;> aesop
    <;> simp_all
    <;> norm_num
    <;> aesop
  
  have h10 : Nat.gcd 19 1 = 1 := by
    -- Simplify the given conditions using the properties of gcd
    simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
    -- Verify that the gcd of 19 and 1 is indeed 1
    <;> norm_num
    <;> rfl
    <;> decide
    <;> decide
    <;> decide
  
  have h11 : Nat.gcd 20! 200000 = Nat.gcd (2^18 * 3^8 * 5^4 * 7^2 * 11 * 13 * 17 * 19) (2^6 * 5^5) := by
    -- Simplify the expression by using the given equalities and properties of gcd
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Nat.gcd_mul_left, Nat.gcd_mul_right, Nat.gcd_assoc]
    -- Use the decide tactic to verify the final result
    <;> decide
  
  have h12 : Nat.gcd (2^18 * 3^8 * 5^4 * 7^2 * 11 * 13 * 17 * 19) (2^6 * 5^5) = 2^6 * 5^4 := by
    simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
    <;> norm_num
    <;> rfl
  
  have h13 : 2^6 * 5^4 = 40000 := by
    simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
    <;> norm_num
    <;> ring_nf
    <;> rfl
    <;> simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
    <;> norm_num
    <;> ring_nf
    <;> rfl
  
  simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
  <;> norm_num
  <;> rfl
  <;> apply h13
  <;> apply h12
  <;> apply h11
  <;> apply h10
  <;> apply h9
  <;> apply h8
  <;> apply h7
  <;> apply h6
  <;> apply h5
  <;> apply h4
  <;> apply h3
  <;> apply h2
  <;> apply h1