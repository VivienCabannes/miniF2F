import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 1600000

theorem imo_1979_p1 (p q : ℕ) (h₀ : 0 < q)
  (h₁ : (∑ k ∈ Finset.Icc (1 : ℕ) 1319, (-1) ^ (k + 1) * ((1 : ℝ) / k)) = p / q) : 1979 ∣ p := by
  -- The alternating harmonic sum 1 - 1/2 + ... + 1/1319 = sum_{k=660}^{1319} 1/k
  -- = sum_{k=660}^{989} (1/k + 1/(1979-k)) = 1979 * sum_{k=660}^{989} 1/(k*(1979-k))
  -- Since 1979 is prime and doesn't divide any k*(1979-k) for 660 ≤ k ≤ 989,
  -- the sum has numerator divisible by 1979.
  sorry
