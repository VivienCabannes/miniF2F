import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_299 :
  (1 * 3 * 5 * 7 * 9 * 11 * 13) % 10 = 5 := by
  have h₀ : (1 * 3 * 5 * 7 * 9 * 11 * 13 : ℕ) % 10 = 5 := by
    norm_num [mul_assoc, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt,
      Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
      Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    <;> rfl
  
  exact h₀