import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_3 :
  (∑ x ∈ Finset.range 10, ((x + 1)^2)) % 10 = 5 := by
  have h_sum : (∑ x in Finset.range 10, (x + 1) ^ 2) % 10 = 5 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Nat.pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
    <;> rfl
  
  exact h_sum