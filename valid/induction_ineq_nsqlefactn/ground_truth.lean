import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_ineq_nsqlefactn (n : ℕ) (h₀ : 4 ≤ n) : n ^ 2 ≤ n ! := by
  have base_case : 4 ^ 2 ≤ 4 ! := by
    induction' h₀ with h₀ IH
    -- Base case: n = 4
    -- 4^2 = 16 and 4! = 24, so 16 ≤ 24
    simp [Nat.factorial]
    -- Inductive step: Assume k^2 ≤ k!
    -- We need to show (k+1)^2 ≤ (k+1)!
    all_goals simp_all [Nat.factorial, Nat.pow_succ]
    -- Simplify the expressions and use the inductive hypothesis
    all_goals nlinarith
    -- Use non-linear arithmetic to conclude the proof
    <;> linarith
  
  have inductive_step : ∀ k ≥ 4, k ^ 2 ≤ k ! → (k + 1) ^ 2 ≤ (k + 1) ! := by
    intro k h₁ h₂
    induction' h₁ with k h₁ ih
    · -- Base case: k = 4
      simp_all [Nat.factorial]
    -- Inductive step: Assume k^2 ≤ k!, prove (k+1)^2 ≤ (k+1)!
    simp_all [Nat.factorial, Nat.mul_comm]
    -- Use nlinarith to handle the arithmetic and inequalities
    all_goals nlinarith
  
  have final_proof : ∀ n ≥ 4, n ^ 2 ≤ n ! := by
    intro n hn
    induction' hn with k hk
    -- Base case: n = 4
    case refl => exact base_case
    -- Inductive step: Assume k^2 ≤ k!, prove (k+1)^2 ≤ (k+1)!
    case step =>
      apply inductive_step k hk
      -- Use the inductive hypothesis to prove the next step
      exact by assumption
  
  have h₁ : n ^ 2 ≤ n ! := by
    apply final_proof
    exact h₀
  exact h₁