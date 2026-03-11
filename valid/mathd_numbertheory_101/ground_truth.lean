import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_101 : 17 * 18 % 4 = 2 := by
  have h17 : 17 % 4 = 1 := by
    -- Step 1: Understand the division
    -- Step 2: Express 17 as a list of 4's
    -- Step 3: Find the remainder after 17 is divided by 4
    -- Step 4: Practice subtracting 4's from 17
    -- Step 5: Make a table of remainders
    -- Step 6: See the cycle repeat
    simp
  
  have h18 : 18 % 4 = 2 := by
    -- We use the fact that 17 % 4 = 1 to help us find the remainder when 18 is divided by 4.
    simp [*, Nat.mod_eq_of_lt, show 1 < 4 by norm_num, show 2 < 4 by norm_num]
    -- Simplifying the expression, we find that 18 % 4 = 2.
    <;> omega
  
  have h_mul : (17 % 4) * (18 % 4) % 4 = (1 * 2) % 4 := by
    -- Simplify the expression using the given properties and basic arithmetic operations.
    simp [h17, h18, Nat.mul_mod, Nat.add_mod, Nat.mod_eq_of_lt, Nat.zero_lt_two, Nat.zero_lt_one]
    -- Use the `decide` tactic to confirm the result of the arithmetic operations.
    <;> decide
  
  have h_final : (1 * 2) % 4 = 2 := by
    simp_all
  
  -- We start by simplifying the given hypotheses to reach the desired conclusion.
  simp_all
  -- `simp_all` will use the given hypotheses to simplify the goal, leading to the conclusion that 17 * 18 % 4 = 2.
  <;> norm_num
  <;> aesop
  <;> norm_num
  <;> aesop