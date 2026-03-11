import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2021_p9 :
  ∏ k ∈ Finset.range 7, (2^(2^k) + 3^(2^k)) = 3^128 - 2^128 := by
  have h₀ : (∏ k in Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k)) = 3 ^ 128 - 2 ^ 128 := by
    norm_num [Finset.prod_range_succ, pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib,
      Finset.prod_range_succ, pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
    <;> rfl
  
  exact h₀