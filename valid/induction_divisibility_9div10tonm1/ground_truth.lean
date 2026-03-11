import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_divisibility_9div10tonm1 (n : ℕ) (h₀ : 0 < n) : 9 ∣ 10 ^ n - 1 := by
  have base_case : 9 ∣ 10 ^ 1 - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    norm_num
    <;> rfl
    <;> simp_all [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, Nat.mod_eq_of_lt]
    <;> norm_num
    <;> omega
  
  have inductive_hypothesis : ∀ k, 0 < k → 9 ∣ 10 ^ k - 1 := by
    -- Introduce the variable k and the assumption that k is positive.
    intro k hk
    -- Use induction on k to prove the statement for all positive integers.
    induction' hk with k hk
    -- Base case: when k = 1, 10^1 - 1 = 9, which is divisible by 9.
    exact base_case
    -- Inductive step: assume 9 divides 10^k - 1, we need to show it divides 10^(k+1) - 1.
    -- Express 10^(k+1) - 1 in terms of 10^k.
    rw [Nat.pow_succ]
    -- Use the fact that 10^(k+1) - 1 = 10 * 10^k - 1.
    -- Rewrite the expression to show it is divisible by 9.
    omega
  
  have inductive_step : ∀ k, 0 < k → 9 ∣ 10 ^ (k + 1) - 1 := by
    intro k hk
    -- Use the inductive hypothesis to prove the statement for k + 1
    apply Nat.dvd_of_mod_eq_zero
    -- Simplify the expression using modular arithmetic properties
    rw [← Nat.mod_add_div (10 ^ (k + 1)) 9]
    -- Normalize the expression to show it is divisible by 9
    norm_num
    -- Simplify the powers and modular arithmetic expressions
    rw [pow_succ]
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod]
    -- Use the inductive hypothesis to conclude the proof
    <;> simp [inductive_hypothesis]
    <;> omega
  
  have conclusion : ∀ n, 0 < n → 9 ∣ 10 ^ n - 1 := by
    intro n hn
    have h₁ := inductive_hypothesis n hn
    have h₂ := inductive_step n hn
    simp_all [Nat.dvd_iff_mod_eq_zero]
    -- Use the inductive hypothesis and the inductive step to simplify the proof
    <;> omega
  
  -- Use the given inductive hypothesis to conclude the proof.
  exact conclusion n h₀