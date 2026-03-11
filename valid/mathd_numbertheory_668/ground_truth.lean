import Mathlib

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_668 (l r : ZMod 7) (h₀ : l = (2 + 3)⁻¹) (h₁ : r = 2⁻¹ + 3⁻¹) :
  l - r = 1 := by
  subst h₀; subst h₁
  have h5 : (5 : ZMod 7)⁻¹ = 3 := ZMod.inv_eq_of_mul_eq_one 7 5 3 (by decide)
  have h2 : (2 : ZMod 7)⁻¹ = 4 := ZMod.inv_eq_of_mul_eq_one 7 2 4 (by decide)
  have h3 : (3 : ZMod 7)⁻¹ = 5 := ZMod.inv_eq_of_mul_eq_one 7 3 5 (by decide)
  simp only [show (2 : ZMod 7) + 3 = 5 from by decide, h5, h2, h3]
  decide
