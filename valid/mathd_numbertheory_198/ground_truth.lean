import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_198 : 5 ^ 2005 % 100 = 25 := by
  have base_case : 5 ^ 2 % 100 = 25 := by
    -- Calculate 5^2 and then find the remainder when divided by 100.
    norm_num
    -- Verify that the result is 25.
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
    <;> rfl
  
  have inductive_step : ∀ k : ℕ, k ≥ 2 → 5 ^ k % 100 = 25 → 5 ^ (k + 1) % 100 = 25 := by
    intro k hk h
    rw [pow_succ]
    norm_num [Nat.mul_mod, h]
    <;> simp [hk]
    <;> norm_num
    <;> omega
  
  have general_pattern : ∀ n : ℕ, n ≥ 2 → 5 ^ n % 100 = 25 := by
    intro n hn
    induction' hn with k hk
    case refl => simp [base_case]
    case step => simp_all [inductive_step]
  
  have result : 5 ^ 2005 % 100 = 25 := by
    apply general_pattern
    norm_num
    <;> simp_all
    <;> norm_num
    <;> linarith
  
  apply result