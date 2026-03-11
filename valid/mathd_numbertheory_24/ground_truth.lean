import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_24 : (∑ k ∈ Finset.Icc 1 9, 11 ^ k) % 100 = 59 := by
  have h1 : 11^1 % 100 = 11 := by
    norm_num
    -- This tactic is used to simplify the expression and verify the result directly.
    -- It checks that 11^1 % 100 equals 11, confirming the result.
    <;> rfl
    -- This tactic ensures that the statement is reflexively true, confirming that 11^1 % 100 indeed equals 11.
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
  
  have h2 : 11^2 % 100 = 21 := by
    -- Use the fact that 11^2 = 121 to compute 121 % 100
    norm_num [pow_succ]
    -- Simplify the expression to show that 121 % 100 = 21
    <;> decide
    <;> simp_all
    <;> decide
  
  have h3 : 11^3 % 100 = 31 := by
    -- Calculate 11 squared mod 100, which is 21
    have h3 : 11^2 % 100 = 21 := h2
    -- Calculate 11 cubed mod 100 by multiplying the previous result by 11
    have h4 : 11^3 % 100 = 31 := by
      -- Use the property of exponents to express 11^3 as 11^2 * 11
      rw [pow_succ]
      -- Use the property of modular arithmetic to simplify the expression
      norm_num [Nat.mul_mod, h3, h1]
    -- The result is 31
    exact h4
  
  have h4 : 11^4 % 100 = 41 := by
    -- Simplify the expression for 11^4 using the given modular equivalences and properties of modular arithmetic.
    norm_num [pow_succ, mul_mod, h1, h2, h3]
    -- Use the omega tactic to solve the resulting linear arithmetic problem.
    <;> omega
  
  have h5 : 11^5 % 100 = 51 := by
    norm_num [pow_succ, Nat.mul_mod, Nat.add_mod, h1, h2, h3, h4]
    -- This tactic uses the given properties to compute the modulus of each power of 11 up to 11^5, confirming the pattern.
    <;> rfl
    -- This ensures that the computed values are consistent with the expected pattern.
    <;> norm_num
    -- This normalizes the numbers to ensure they fit within the expected range.
    <;> rfl
  
  have h6 : 11^6 % 100 = 61 := by
    norm_num [pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
    <;> simp_all [Nat.pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
    <;> norm_num
    <;> omega
  
  have h7 : 11^7 % 100 = 71 := by
    -- Normalize the numbers to simplify the calculation
    norm_num [h1, h2, h3, h4, h5, h6]
    -- Use the `decide` tactic to confirm the result
    <;> decide
    -- Simplify the expression using `ring_nf`
    <;> ring_nf
    -- Use `norm_num` again to finalize the calculation
    <;> norm_num
    -- Use `decide` to confirm the final result
    <;> decide
  
  have h8 : 11^8 % 100 = 81 := by
    -- We use the fact that 11^8 % 100 can be computed by multiplying the remainders of the previous powers of 11 modulo 100.
    norm_num [pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
    <;> simp [h1, h2, h3, h4, h5, h6, h7]
    <;> rfl
  
  have h9 : 11^9 % 100 = 91 := by
    -- We observe that the pattern of the last two digits repeats every 20 powers.
    -- Therefore, we can use the given results to find the last two digits of 11^9.
    norm_num [pow_succ, h1, h2, h3, h4, h5, h6, h7, h8, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
    -- This tactic uses the given results and modular arithmetic properties to compute the last two digits of 11^9.
    <;> rfl
    -- This confirms that the computed value matches the expected result.
    <;> simp_all [Nat.pow_succ]
    -- This simplifies the expression to ensure the correctness of the result.
    <;> norm_num
    -- This normalizes the numerical expression to ensure the correctness of the result.
    <;> rfl
  
  have sum_terms : (11 + 21 + 31 + 41 + 51 + 61 + 71 + 81 + 91) % 100 = 59 := by
    -- Simplify the sum using the given modular equivalences and properties of modular arithmetic.
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    -- Use the `decide` tactic to verify the final result.
    <;> decide
  
  simp_all [Finset.sum_range_succ, Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  <;> rfl
  <;> rfl
  <;> rfl