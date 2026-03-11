import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_728 :
  (29^13 - 5^13) % 7 = 3 := by
  have h₁ : 29 ^ 13 % 7 = 1 := by
    norm_num [Nat.pow_mod, Nat.mod_mod, Nat.mod_eq_of_lt, show 2 ≤ 7 by norm_num]
    <;> rfl
  
  have h₂ : 5 ^ 13 % 7 = 5 := by
    norm_num [Nat.pow_mod, Nat.mod_mod, Nat.mod_eq_of_lt, show 2 ≤ 7 by norm_num]
    <;> rfl
  
  have h₃ : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
    have h₄ : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
      omega
    exact h₄
  
  apply h₃