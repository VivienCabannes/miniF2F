import Mathlib

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_427
  (a : ℕ)
  (h₀ : a = (∑ k ∈ (Nat.divisors 500), k)) :
  ∑ k ∈ Finset.filter (λ x => Nat.Prime x) (Nat.divisors a), k = 25 := by sorry
