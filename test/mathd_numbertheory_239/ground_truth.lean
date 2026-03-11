import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_239 :
  (∑ k ∈ Finset.Icc 1 12, k) % 4 = 2 := by
  have h_sum : (∑ k in Finset.Icc 1 12, k) = 78 := by
    norm_num [Finset.sum_Icc_succ_top, Nat.div_eq_of_lt]
    <;> rfl
  
  have h_final : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by
    rw [h_sum]
    <;> norm_num
    <;> rfl
  
  apply h_final