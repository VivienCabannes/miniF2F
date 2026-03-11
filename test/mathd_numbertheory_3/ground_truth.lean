import Mathlib

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_3 :
  (∑ x ∈ Finset.range 10, ((x + 1)^2)) % 10 = 5 := by sorry
