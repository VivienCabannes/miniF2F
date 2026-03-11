import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_237 :
  (∑ k ∈ (Finset.range 101), k) % 6 = 4 := by
  have h : (∑ k in Finset.range 101, k) = 5050 := by
    rfl
  
  have h₁ : (∑ k in Finset.range 101, k) % 6 = 4 := by
    rw [h]
    <;> norm_num
    <;> rfl
  
  apply h₁