import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 800000

theorem numbertheory_xsqpysqintdenomeq (x y : ℚ) (h₀ : (x ^ 2 + y ^ 2).den = 1) : x.den = y.den := by
  have hint : ((x ^ 2 + y ^ 2).num : ℚ) = x ^ 2 + y ^ 2 :=
    Rat.coe_int_num_of_den_eq_one h₀
  have hx2 : x ^ 2 = ↑(x ^ 2 + y ^ 2).num - y ^ 2 := by linarith
  have hden_eq : (x ^ 2).den = (y ^ 2).den := by
    rw [hx2]
    exact Rat.intCast_sub_den _ _
  simp only [Rat.den_pow] at hden_eq
  exact Nat.pow_left_injective (n := 2) (by norm_num) hden_eq
