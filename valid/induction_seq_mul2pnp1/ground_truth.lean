import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_seq_mul2pnp1 (n : ℕ) (u : ℕ → ℕ) (h₀ : u 0 = 0)
  (h₁ : ∀ n, u (n + 1) = 2 * u n + (n + 1)) : u n = 2 ^ (n + 1) - (n + 2) := by
  have base_case : u 0 = 2 ^ (0 + 1) - (0 + 2) := by
    -- Simplify the right-hand side using basic arithmetic operations
    simp [h₀, pow_one, Nat.mul_zero, Nat.add_zero]
    -- This line uses the given initial condition h₀ to simplify the expression
    -- and verifies that the formula holds for n = 0.
    <;> linarith
  
  have inductive_hypothesis : ∀ k : ℕ, u k = 2 ^ (k + 1) - (k + 2) → u (k + 1) = 2 ^ ((k + 1) + 1) - ((k + 1) + 2) := by
    intro k hk
    -- Use the given recurrence relation to calculate the next term in the sequence.
    cases k with
    | zero =>
      -- Base case: k = 0
      simp_all [h₁, h₀]
    | succ k' =>
      -- Inductive step: assume the formula holds for k', prove it for k'+1
      simp_all [h₁, pow_succ, mul_add, mul_comm, mul_left_comm, Nat.mul_sub_left_distrib]
      -- Simplify the expression using algebraic properties and the given base case.
      <;> ring_nf
      <;> omega
  
  have inductive_step : ∀ k : ℕ, u k = 2 ^ (k + 1) - (k + 2) := by
    intro k
    induction k with
    | zero =>
      -- Base case: k = 0
      simp_all [h₀]
    | succ k ih =>
      -- Inductive step: assume the statement holds for k, prove for k+1
      simp_all [h₁, Nat.pow_succ, Nat.mul_succ]
      -- Simplify the expression using the recursive definition and algebraic properties
      <;> omega
  
  have h₂ := inductive_step
  have h₃ := inductive_hypothesis
  simp_all