import Mathlib

open BigOperators Real Nat Topology Rat

-- Quick test: can we compute the product?
#eval ∏ i ∈ (Finset.Icc 1 9), i !
-- Should be 1834588569600

-- Quick test: can we compute divisors count?
#eval (Nat.divisors (2^15 * 3^6 * 5^2 * 7)).card
