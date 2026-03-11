import Mathlib
import Aesop

set_option maxHeartbeats 800000

open BigOperators Real Nat Topology Rat

theorem aime_1987_p5
  (x y : ℤ)
  (h₀ : y^2 + 3 * (x^2 * y^2) = 30 * x^2 + 517):
  3 * (x^2 * y^2) = 588 := by
  have h_ne : x ≠ 0 := by
    intro hx; subst hx; simp at h₀
    have : y ≤ 22 := by nlinarith [sq_nonneg y]
    have : y ≥ -22 := by nlinarith [sq_nonneg y]
    interval_cases y <;> omega
  have h_factor : (3 * x ^ 2 + 1) * y ^ 2 = 30 * x ^ 2 + 517 := by nlinarith
  have h_dvd : (3 * x ^ 2 + 1 : ℤ) ∣ 507 := by
    have h1 : (3 * x ^ 2 + 1) ∣ (30 * x ^ 2 + 517) := ⟨y ^ 2, h_factor.symm⟩
    have h2 : (30 * x ^ 2 + 517 : ℤ) = 10 * (3 * x ^ 2 + 1) + 507 := by ring
    rwa [h2, dvd_add_right (dvd_mul_left _ _)] at h1
  have h_xsq : x ^ 2 = 4 := by
    have h_le : 3 * x ^ 2 + 1 ≤ 507 := Int.le_of_dvd (by norm_num) h_dvd
    have : x ≤ 12 := by nlinarith [sq_nonneg x]
    have : x ≥ -12 := by nlinarith [sq_nonneg x]
    interval_cases x <;> omega
  have h_ysq : y ^ 2 = 49 := by nlinarith
  nlinarith
