import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_202 : (19 ^ 19 + 99 ^ 99) % 10 = 8 := by
  have h₁ : 19 % 10 = 9 := by
    -- Use the `simp` tactic to simplify the expression `19 % 10`.
    -- The `simp` tactic will automatically apply the definition of the modulo operation and simplify the expression to 9.
    simp [Int.emod_eq_of_lt]
    -- The `norm_num` tactic is used to verify the numerical result, ensuring that the simplification is correct.
    <;> norm_num
    -- The `decide` tactic is used to confirm the logical result, ensuring that the simplification is correct.
    <;> decide
    <;> norm_num
    <;> decide
  
  have h₂ : 99 % 10 = 9 := by
    -- Use the given lemma to simplify the proof
    simp_all [Nat.mod_eq_of_lt, show 19 % 10 = 9 by norm_num, show 99 % 10 = 9 by norm_num]
  
  have h₃ : 9^19 % 10 = 9 := by
    -- Use norm_num to simplify the expression modulo 10
    norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
    -- The above tactic will simplify the powers of 9 modulo 10, showing that 9^19 % 10 = 9
    <;> rfl
  
  have h₄ : 9^99 % 10 = 9 := by
    -- We observe that the last digits of powers of 9 follow a pattern: 9, 1, 9, 1, ...
    -- This pattern repeats every two exponents.
    norm_num [pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at h₃ ⊢
    -- Using the pattern, we can determine that 9^99 has the same last digit as 9^19.
    <;> aesop
  
  have h₅ : (9 + 9) % 10 = 8 := by
    -- Simplify the expression (9 + 9) % 10 using basic arithmetic operations.
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
    <;> simp_all
    <;> norm_num
    <;> rfl
  
  simp_all [Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
  <;> norm_num
  <;> rfl