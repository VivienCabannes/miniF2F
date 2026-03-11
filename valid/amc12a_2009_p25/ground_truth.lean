import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 12800000

theorem amc12a_2009_p25 (a : ℕ → ℝ) (h₀ : a 1 = 1) (h₁ : a 2 = 1 / Real.sqrt 3)
  (h₂ : ∀ n, 1 ≤ n → a (n + 2) = (a n + a (n + 1)) / (1 - a n * a (n + 1))) :
    abs (a 2009) = 0 := by
  set s := Real.sqrt 3 with hs_def
  have hs_pos : (0 : ℝ) < s := Real.sqrt_pos_of_pos (by norm_num)
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hss : s * s = 3 := Real.mul_self_sqrt (by norm_num)
  have hs_gt1 : s > 1 := by nlinarith [hss]
  have hsm1 : s - 1 ≠ 0 := by linarith
  have hsp1 : s + 1 ≠ 0 := by linarith
  -- Denominator nonzero helper: prove by contradiction
  -- pattern: intro habs; field_simp at habs; nlinarith [hss]
  -- a(3) = (s + 1) / (s - 1)
  have ha3 : a 3 = (s + 1) / (s - 1) := by
    have := h₂ 1 le_rfl; rw [this, h₀, h₁]; field_simp
  -- a(4) = -((s + 1) / (s - 1))
  have ha4 : a 4 = -((s + 1) / (s - 1)) := by
    have := h₂ 2 (by norm_num); rw [this, h₁, ha3]
    have hd : 1 - 1 / s * ((s + 1) / (s - 1)) ≠ 0 := by
      intro habs; field_simp at habs; nlinarith [hss]
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(5) = 0
  have ha5 : a 5 = 0 := by
    have := h₂ 3 (by norm_num); rw [this, ha3, ha4]
    simp [add_neg_cancel, zero_div]
  -- a(6) = -((s + 1) / (s - 1))
  have ha6 : a 6 = -((s + 1) / (s - 1)) := by
    have := h₂ 4 (by norm_num); rw [this, ha4, ha5]; simp
  -- a(7) = -((s + 1) / (s - 1))
  have ha7 : a 7 = -((s + 1) / (s - 1)) := by
    have := h₂ 5 (by norm_num); rw [this, ha5, ha6]; simp
  -- a(8) = 1 / s
  have ha8 : a 8 = 1 / s := by
    have := h₂ 6 (by norm_num); rw [this, ha6, ha7]
    have hd : 1 - -((s + 1) / (s - 1)) * -((s + 1) / (s - 1)) ≠ 0 := by
      intro habs; field_simp at habs; nlinarith [hss]
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(9) = -1
  have ha9 : a 9 = -1 := by
    have := h₂ 7 (by norm_num); rw [this, ha7, ha8]
    have hd : 1 - -((s + 1) / (s - 1)) * (1 / s) ≠ 0 := by
      intro habs; field_simp at habs; nlinarith [hss]
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(10) = s - 2
  have ha10 : a 10 = s - 2 := by
    have := h₂ 8 (by norm_num); rw [this, ha8, ha9]
    have hd : (1 : ℝ) - 1 / s * (-1) ≠ 0 := by
      intro habs; field_simp at habs; linarith
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(11) = -s
  have ha11 : a 11 = -s := by
    have := h₂ 9 (by norm_num); rw [this, ha9, ha10]
    have hd : (1 : ℝ) - (-1) * (s - 2) ≠ 0 := by
      intro habs; linarith
    rw [div_eq_iff hd]; nlinarith [hss]
  -- a(12) = -(s + 2)
  have ha12 : a 12 = -(s + 2) := by
    have := h₂ 10 (by norm_num); rw [this, ha10, ha11]
    have hd : 1 - (s - 2) * (-s) ≠ 0 := by nlinarith [hss]
    rw [div_eq_iff hd]; nlinarith [hss]
  -- a(13) = 1
  have ha13 : a 13 = 1 := by
    have := h₂ 11 (by norm_num); rw [this, ha11, ha12]
    have hd : 1 - (-s) * (-(s + 2)) ≠ 0 := by nlinarith [hss]
    rw [div_eq_iff hd]; nlinarith [hss]
  -- a(14) = -(1/s)
  have ha14 : a 14 = -(1 / s) := by
    have := h₂ 12 (by norm_num); rw [this, ha12, ha13]
    have hd : (1 : ℝ) - (-(s + 2)) * 1 ≠ 0 := by nlinarith
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(15) = 2 - s
  have ha15 : a 15 = 2 - s := by
    have := h₂ 13 (by norm_num); rw [this, ha13, ha14]
    have hd : (1 : ℝ) - 1 * (-(1 / s)) ≠ 0 := by
      intro habs; field_simp at habs; linarith
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(16) = s - 2
  have ha16 : a 16 = s - 2 := by
    have := h₂ 14 (by norm_num); rw [this, ha14, ha15]
    have hd : (1 : ℝ) - -(1 / s) * (2 - s) ≠ 0 := by
      intro habs; field_simp at habs; linarith
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(17) = 0
  have ha17 : a 17 = 0 := by
    have := h₂ 15 (by norm_num); rw [this, ha15, ha16]
    have : (2 - s + (s - 2)) = 0 := by ring
    simp [this]
  -- a(18) = s - 2
  have ha18 : a 18 = s - 2 := by
    have := h₂ 16 (by norm_num); rw [this, ha16, ha17]; simp
  -- a(19) = s - 2
  have ha19 : a 19 = s - 2 := by
    have := h₂ 17 (by norm_num); rw [this, ha17, ha18]; simp
  -- a(20) = -(1/s)
  have ha20 : a 20 = -(1 / s) := by
    have := h₂ 18 (by norm_num); rw [this, ha18, ha19]
    have hd : 1 - (s - 2) * (s - 2) ≠ 0 := by nlinarith [hss]
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(21) = -1
  have ha21 : a 21 = -1 := by
    have := h₂ 19 (by norm_num); rw [this, ha19, ha20]
    have hd : (1 : ℝ) - (s - 2) * (-(1 / s)) ≠ 0 := by
      intro habs; field_simp at habs; linarith
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(22) = -((s + 1) / (s - 1))
  have ha22 : a 22 = -((s + 1) / (s - 1)) := by
    have := h₂ 20 (by norm_num); rw [this, ha20, ha21]
    have hd : (1 : ℝ) - -(1 / s) * (-1) ≠ 0 := by
      intro habs; field_simp at habs; linarith
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(23) = s
  have ha23 : a 23 = s := by
    have := h₂ 21 (by norm_num); rw [this, ha21, ha22]
    have hsm1 : s - 1 ≠ 0 := by linarith
    rw [show (-1 : ℝ) + -((s + 1) / (s - 1)) = -(2 * s) / (s - 1) from by field_simp; ring]
    rw [show (1 : ℝ) - (-1) * -((s + 1) / (s - 1)) = -(2 : ℝ) / (s - 1) from by field_simp; ring]
    rw [div_div_div_cancel_right₀ hsm1]
    simp only [neg_div_neg_eq]
    rw [div_eq_iff (show (2 : ℝ) ≠ 0 by norm_num)]
    ring
  -- a(24) = -((s - 1) / (s + 1))
  have ha24 : a 24 = -((s - 1) / (s + 1)) := by
    have := h₂ 22 (by norm_num); rw [this, ha22, ha23]
    have hd : (1 : ℝ) - -((s + 1) / (s - 1)) * s ≠ 0 := by
      intro habs; field_simp at habs; nlinarith [hss]
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(25) = 1
  have ha25 : a 25 = 1 := by
    have := h₂ 23 (by norm_num); rw [this, ha23, ha24]
    have hd : (1 : ℝ) - s * -((s - 1) / (s + 1)) ≠ 0 := by
      intro habs; field_simp at habs; nlinarith [hss]
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- a(26) = 1/s
  have ha26 : a 26 = 1 / s := by
    have := h₂ 24 (by norm_num); rw [this, ha24, ha25]
    have hd : (1 : ℝ) - -((s - 1) / (s + 1)) * 1 ≠ 0 := by
      intro habs; field_simp at habs; linarith
    rw [div_eq_iff hd]; field_simp; nlinarith [hss]
  -- Periodicity: a(n + 24) = a(n) for all n >= 1
  have hperiod : ∀ n, 1 ≤ n → a (n + 24) = a n := by
    suffices key : ∀ k, 1 ≤ k → (∀ j, 1 ≤ j → j < k → a (j + 24) = a j) → a (k + 24) = a k by
      intro n hn
      induction n using Nat.strongRecOn with
      | ind n ih => exact key n hn (fun j hj hjn => ih j hjn hj)
    intro k hk ih
    match k, hk with
    | 1, _ => show a 25 = a 1; rw [ha25, h₀]
    | 2, _ => show a 26 = a 2; rw [ha26, h₁]
    | k + 3, _ =>
      have ih1 : a (k + 1 + 24) = a (k + 1) := ih (k + 1) (by omega) (by omega)
      have ih2 : a (k + 2 + 24) = a (k + 2) := ih (k + 2) (by omega) (by omega)
      show a (k + 3 + 24) = a (k + 3)
      have eq1 : k + 3 + 24 = (k + 1 + 24) + 2 := by omega
      have eq2 : (k + 1 + 24) + 1 = k + 2 + 24 := by omega
      have eq3 : k + 3 = (k + 1) + 2 := by omega
      have eq4 : (k + 1) + 1 = k + 2 := by omega
      rw [eq1, h₂ (k + 1 + 24) (by omega), eq2, ih1, ih2,
          eq3, h₂ (k + 1) (by omega), eq4]
  -- 2009 = 17 + 24 * 83
  have h2009 : a 2009 = a 17 := by
    have hiter : ∀ k : ℕ, a (17 + 24 * k) = a 17 := by
      intro k; induction k with
      | zero => simp
      | succ k ihk =>
        rw [show 17 + 24 * (k + 1) = (17 + 24 * k) + 24 from by ring,
            hperiod (17 + 24 * k) (by omega), ihk]
    rw [show (2009 : ℕ) = 17 + 24 * 83 from by norm_num, hiter 83]
  rw [h2009, ha17, abs_zero]
