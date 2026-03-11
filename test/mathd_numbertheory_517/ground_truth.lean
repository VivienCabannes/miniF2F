import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_517 :
  (121 * 122 * 123) % 4 = 2 := by
  have h₁ : 121 % 4 = 1 := by
    norm_num
    <;> rfl
  
  have h₂ : 122 % 4 = 2 := by
    norm_num
    <;> rfl
  
  have h₃ : 123 % 4 = 3 := by
    norm_num
    <;> rfl
  
  have h₄ : 121 * 122 * 123 % 4 = 2 := by
    norm_num [h₁, h₂, h₃, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt]
    <;>
    rfl
  
  apply h₄