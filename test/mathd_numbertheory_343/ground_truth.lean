import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_343 :
  (∏ k ∈ Finset.range 6, (2 * k + 1)) % 10 = 5 := by
  have h₁ : (∏ k in Finset.range 6, (2 * k + 1)) = 1 * 3 * 5 * 7 * 9 * 11 := by
    norm_num [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    <;> decide
  
  have h₂ : (∏ k in Finset.range 6, (2 * k + 1)) % 10 = 5 := by
    rw [h₁]
    <;> norm_num
    <;> rfl
  
  apply h₂