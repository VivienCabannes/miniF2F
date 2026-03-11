import Mathlib

open BigOperators Real Nat Topology Rat

-- Explore the types involved
#check @Rat.num
#check @Rat.den
#check Rat.num_div_den

theorem amc12a_2020_p25
  (a : ℚ)
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ ↑⌊x⌋ * (x - ↑⌊x⌋) = ↑a * x ^ 2)
  (h₁ : ∑ k ∈ S, k = 420) :
  ↑a.den + a.num = 929 := by sorry
