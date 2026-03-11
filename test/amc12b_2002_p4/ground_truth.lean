import Mathlib

open BigOperators Real Nat Topology Rat

theorem amc12b_2002_p4
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ((1 / 2 + 1 / 3 + 1 / 7 + 1 / n) : ℚ).den = 1) :
  n = 42 := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Rewrite: 1/2 + 1/3 + 1/7 + 1/n = (41n + 42)/(42n)
  have hsum : (1 / 2 + 1 / 3 + 1 / 7 + 1 / (n : ℚ)) = (41 * n + 42) / (42 * n) := by
    field_simp; ring
  rw [hsum] at h₁
  -- den = 1 means (41n+42)/(42n) is an integer
  have hnum_eq := Rat.coe_int_num_of_den_eq_one h₁
  set z := ((41 * (n : ℚ) + 42) / (42 * n)).num
  -- z * (42n) = 41n + 42 in ℚ, hence in ℤ
  have hzq : (z : ℚ) * (42 * n) = 41 * n + 42 := by
    rw [hnum_eq]; field_simp
  -- Cast to ℤ
  have hzi : z * (42 * (n : ℤ)) = 41 * n + 42 := by exact_mod_cast hzq
  -- z must be positive (since 41n + 42 > 0 and 42n > 0)
  have h42n_pos : (0 : ℤ) < 42 * n := by omega
  have hrhs_pos : (0 : ℤ) < 41 * n + 42 := by omega
  have hz_pos : 0 < z := by
    by_contra h
    push_neg at h
    have : z * (42 * (n : ℤ)) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    omega
  -- z ≤ 1 (otherwise 2 * 42n > 41n + 42 for n ≥ 1)
  have hz_le : z ≤ 1 := by
    by_contra h
    push_neg at h
    have : 2 * (42 * (n : ℤ)) ≤ z * (42 * n) :=
      mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  -- So z = 1
  have hz_eq : z = 1 := by omega
  -- 42n = 41n + 42, hence n = 42
  have : 1 * (42 * (n : ℤ)) = 41 * n + 42 := by rw [← hz_eq]; exact hzi
  have : (n : ℤ) = 42 := by linarith
  exact_mod_cast this
