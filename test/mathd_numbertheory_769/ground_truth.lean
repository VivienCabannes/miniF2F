import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_769 :
  (129^34 + 96^38) % 11 = 9 := by
  have h1 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by
    norm_num [Nat.add_mod, Nat.pow_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
      show 2 ≤ 11 by decide, show 2 ≤ 11 by decide]
    <;>
    rfl
  exact h1