import Mathlib

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_419
  (a b : ℝ)
  (h₀ : a = -1)
  (h₁ : b = 5) :
  -a - b^2 + 3 * (a * b) = -39 := by subst h₀; subst h₁; norm_num
