import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_sum2kp1npqsqm1 (n : ℕ) :
  ∑ k ∈ Finset.range n, (2 * k + 3) = (n + 1) ^ 2 - 1 := by
  have base_case : ∑ k in Finset.range 1, (2 * k + 3) = (1 + 1) ^ 2 - 1 := by
    -- Simplify the left-hand side of the equation by evaluating the sum.
    simp
    -- The sum of the left-hand side for k=0 is 3, which matches the right-hand side for n=1.
    <;> rfl
  
  have inductive_hypothesis : ∀ m : ℕ, ∑ k in Finset.range m, (2 * k + 3) = (m + 1) ^ 2 - 1 → 
    ∑ k in Finset.range (m + 1), (2 * k + 3) = ((m + 1) + 1) ^ 2 - 1 := by
    intro m hm
    simp_all [Finset.sum_range_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_one]
    -- Simplify the expression using known properties and algebraic rules.
    <;> linarith
  
  have induction_step : ∀ n : ℕ, ∑ k in Finset.range n, (2 * k + 3) = (n + 1) ^ 2 - 1 := by
    intro n
    have h₁ := base_case
    have h₂ := inductive_hypothesis
    -- Use induction on n
    induction n with
    | zero =>
      -- Base case: n = 0
      simp_all [Finset.sum_range_zero]
    | succ n ih =>
      -- Inductive step: assume the statement holds for n, prove for n + 1
      simp_all [Finset.sum_range_succ, Nat.pow_succ, Nat.mul_succ]
      -- Simplify the expression using algebraic rules
      <;> ring_nf
      -- Use omega to solve the resulting linear arithmetic problem
      <;> omega
  
  induction n with
  | zero =>
    -- Base case: when n = 0, the sum is 0, which matches the formula (0 + 1)^2 - 1 = 0
    simpa using base_case
  | succ n ih =>
    -- Inductive step: assume the formula holds for n, prove it for n + 1
    simpa [Finset.sum_range_succ, Nat.succ_eq_add_one] using inductive_hypothesis n ih