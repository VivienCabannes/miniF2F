import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_342 :
  54 % 6 = 0 := by
  have h : 54 % 6 = 0 := by
    norm_num
    <;> rfl
  
  exact h