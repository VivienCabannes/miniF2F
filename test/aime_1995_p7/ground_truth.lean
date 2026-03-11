import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 800000

theorem aime_1995_p7
  (k m n : ℕ)
  (t : ℝ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 1)
  (h₂ : (1 + Real.sin t) * (1 + Real.cos t) = 5/4)
  (h₃ : (1 - Real.sin t) * (1- Real.cos t) = m/n - Real.sqrt k):
  k + m + n = 27 := by
  set s := Real.sin t + Real.cos t
  have hsin2cos2 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  have hsincos : Real.sin t * Real.cos t = (s ^ 2 - 1) / 2 := by
    rw [show s = Real.sin t + Real.cos t from rfl]
    nlinarith [sq_abs (Real.sin t - Real.cos t)]
  have h2_exp : s + Real.sin t * Real.cos t = 1 / 4 := by nlinarith [h₂]
  have hsp1_sq : (s + 1) ^ 2 = 5 / 2 := by nlinarith
  have hs_sq_le : s ^ 2 ≤ 2 := by
    rw [show s = Real.sin t + Real.cos t from rfl]
    nlinarith [sq_abs (Real.sin t - Real.cos t)]
  have hsp1_pos : s + 1 > 0 := by nlinarith
  have hsp1 : s + 1 = Real.sqrt (5 / 2) := by
    have : (s + 1) ^ 2 = 5 / 2 := hsp1_sq
    rw [← Real.sqrt_sq (le_of_lt hsp1_pos), this]
  have h3_val : (↑m : ℝ) / ↑n - Real.sqrt ↑k = (s - 1) ^ 2 / 2 := by
    nlinarith [h₃, hsincos]
  have h_sm1_sq : (s - 1) ^ 2 = 13 / 2 - 4 * Real.sqrt (5 / 2) := by
    have h52_nn : (0 : ℝ) ≤ 5 / 2 := by norm_num
    have := Real.sq_sqrt h52_nn
    have hs_val : s = Real.sqrt (5 / 2) - 1 := by linarith
    rw [hs_val]; nlinarith
  have h_sqrt10 : Real.sqrt 10 = 2 * Real.sqrt (5 / 2) := by
    rw [show (10 : ℝ) = 2 ^ 2 * (5 / 2) from by ring]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2 ^ 2)]
    simp [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have h_final : (↑m : ℝ) / ↑n - Real.sqrt ↑k = 13 / 4 - Real.sqrt 10 := by
    rw [h3_val, h_sm1_sq, h_sqrt10]; ring
  have h10_irr : Irrational (Real.sqrt 10) := by
    have h10nn : (0:ℝ) ≤ 10 := by norm_num
    apply irrational_nrt_of_notint_nrt 2 10
    · simp [Real.sq_sqrt h10nn]
    · intro ⟨y, hy⟩
      have hsqrt_nn := Real.sqrt_nonneg (10 : ℝ)
      have hy_nn : (0:ℤ) ≤ y := by
        by_contra h; push_neg at h
        have : (y : ℝ) < 0 := Int.cast_lt_zero.mpr h; linarith
      have hy_sq : y * y = 10 := by
        have h1 := Real.sq_sqrt h10nn
        rw [sq, hy, ← Int.cast_mul] at h1; exact_mod_cast h1
      have hy_le : y ≤ 3 := by nlinarith
      interval_cases y <;> omega
    · norm_num
  set r := (↑m : ℝ) / ↑n - 13 / 4 with hr_def
  have h_sqrtk_eq : Real.sqrt ↑k = Real.sqrt 10 + r := by linarith
  have hr_zero : r = 0 := by
    by_contra hr_ne
    have hk_eq : (↑k : ℝ) = (Real.sqrt 10 + r) ^ 2 := by
      have h1 := Real.sq_sqrt (show (0:ℝ) ≤ ↑k from Nat.cast_nonneg k)
      have h2 : Real.sqrt ↑k = Real.sqrt 10 + r := h_sqrtk_eq
      calc (↑k : ℝ) = Real.sqrt ↑k ^ 2 := h1.symm
        _ = (Real.sqrt 10 + r) ^ 2 := by rw [h2]
    have h_2r10 : 2 * r * Real.sqrt 10 = ↑k - 10 - r ^ 2 := by nlinarith
    have h10_rat : ∃ q : ℚ, (q : ℝ) = Real.sqrt 10 := by
      have : ∃ q : ℚ, (q : ℝ) = r := by
        use (m : ℚ) / n - 13 / 4; push_cast; ring
      obtain ⟨qr, hqr⟩ := this
      have hqr_ne : qr ≠ 0 := by intro h; apply hr_ne; rw [← hqr, h]; simp
      have hqr_ne' : (qr : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hqr_ne
      use ((↑k - 10 : ℚ) - qr ^ 2) / (2 * qr)
      rw [Rat.cast_div, Rat.cast_mul]
      rw [div_eq_iff (by push_cast; exact mul_ne_zero two_ne_zero hqr_ne')]
      push_cast
      linarith [hqr ▸ h_2r10]
    exact h10_irr (Set.mem_range.mpr h10_rat)
  have hmn_eq : (↑m : ℝ) / ↑n = 13 / 4 := by linarith
  have hk_eq : Real.sqrt ↑k = Real.sqrt 10 := by linarith
  have hk_val : k = 10 := by
    have h1 := Real.sq_sqrt (show (0:ℝ) ≤ ↑k from Nat.cast_nonneg k)
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ (10:ℝ) from by norm_num)
    have : (↑k : ℝ) = 10 := by nlinarith [hk_eq]
    exact_mod_cast this
  have h4m_13n : 4 * m = 13 * n := by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_eq_div_iff hn' (by norm_num : (4:ℝ) ≠ 0)] at hmn_eq
    have : (4 * m : ℝ) = 13 * n := by linarith
    exact_mod_cast this
  have h13m : 13 ∣ m := by
    have h13_4m : 13 ∣ 4 * m := ⟨n, by omega⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 13 4 by decide) h13_4m
  obtain ⟨j, rfl⟩ := h13m
  have hn_eq : n = 4 * j := by omega
  subst hn_eq
  rw [Nat.gcd_mul_right] at h₁
  norm_num [show Nat.gcd 13 4 = 1 from by decide] at h₁
  rw [hk_val]; omega
