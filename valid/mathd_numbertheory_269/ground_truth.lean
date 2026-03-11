import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_269 : (2005 ^ 2 + 2005 ^ 0 + 2005 ^ 0 + 2005 ^ 5) % 100 = 52 := by
  have simplify_exp : 2005 ^ 2 + 2005 ^ 0 + 2005 ^ 0 + 2005 ^ 5 = 2005 ^ 2 + 2005 ^ 5 + 2 := by
    norm_num
    <;> simp [Nat.pow_succ]
    <;> ring
    <;> norm_num
    <;> rfl
    <;> rfl
  
  have mod_100 : 2005 % 100 = 5 := by
    -- We need to show that 2005 modulo 100 equals 5.
    -- This can be directly verified by computing 2005 modulo 100.
    norm_num [Nat.mod_eq_of_lt, Nat.add_mod, Nat.pow_mod]
    -- The `norm_num` tactic will simplify the expression and compute the result directly.
    -- Since 2005 modulo 100 is 5, the proof is complete.
    <;> rfl
    <;> simp_all
    <;> norm_num
    <;> rfl
  
  have pow2_mod_100 : 2005 ^ 2 % 100 = 25 := by
    -- Calculate 2005 modulo 100 to simplify the problem
    have h : 2005 % 100 = 5 := by norm_num
    -- Simplify the expression 2005^2 modulo 100 using the fact that 2005 ≡ 5 (mod 100)
    norm_num [h, Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    -- Verify the result using numerical computation
    <;> decide
  
  have pow5_mod_100 : 2005 ^ 5 % 100 = 25 := by
    -- Use the properties of modular arithmetic to simplify the problem.
    norm_num [pow_mod, Nat.mod_eq_of_lt, Nat.succ_pos, Nat.zero_lt_one]
    <;> simp_all [Nat.add_mod, Nat.mul_mod, Nat.pow_succ]
    <;> norm_num
    <;> omega
  
  have final_result : (2005 ^ 2 + 2005 ^ 5 + 2) % 100 = 52 := by
    -- Use the properties of modular arithmetic to simplify the expression
    norm_num [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_eq_of_lt]
    <;> simp_all
    <;> decide
    <;> decide
    <;> decide
  
  -- Normalize the numbers to confirm the initial expression is correct.
  norm_num [simplify_exp, pow2_mod_100, pow5_mod_100, final_result]
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl
  <;> rfl