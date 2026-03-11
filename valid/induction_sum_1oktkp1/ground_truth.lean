import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_sum_1oktkp1 (n : ℕ) :
  (∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1) * (k + 2))) = n / (n + 1) := by
  induction n with
  | zero =>
    -- Base case: when n = 0, the sum is trivially 0, which matches the right-hand side.
    norm_num
  | succ n ihn =>
    -- Inductive step: assume the statement holds for n, prove it for n + 1.
    rw [Finset.range_succ, Finset.sum_insert Finset.not_mem_range_self, ihn, add_mul]
    -- Simplify the expression by expanding and simplifying it.
    field_simp
    -- Normalize the expression to achieve the final simplified form.
    ring_nf