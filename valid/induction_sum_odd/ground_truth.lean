import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_sum_odd (n : ℕ) : (∑ k ∈ Finset.range n, (2 * k + 1)) = n ^ 2 := by
  induction' n with n IH
  · -- Base case: when n = 0, the sum is 0, which is 0^2.
    simp
  · -- Inductive step: assume the statement holds for n, prove it for n + 1.
    simp_all [Finset.sum_range_succ, Nat.pow_succ, Nat.mul_succ]
    -- Simplify the expression to match the form (n + 1)^2.
    linarith