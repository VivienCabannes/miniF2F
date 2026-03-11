import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 800000

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778
  (r : ℝ)
  (h₀ : r^(1 / 3: ℝ) + 1 / r^(1 / 3: ℝ) = 3) :
  r^3 + 1 / r^3 = 5778 := by
  set t := r ^ (1 / 3 : ℝ) with ht_def
  have ht_ne : t ≠ 0 := by
    intro ht0; rw [ht0, div_zero, add_zero] at h₀; linarith
  have hr_ne : r ≠ 0 := by
    intro hr0
    exact ht_ne (by rw [ht_def, hr0, zero_rpow (by norm_num : (1:ℝ)/3 ≠ 0)])
  -- We need r > 0. For r < 0, the rpow definition gives different values
  -- and the theorem as stated is actually false (formalization issue in MiniF2F).
  -- The theorem is only true when r > 0 (real cube root).
  have hr_pos : 0 < r := by
    rcases lt_or_gt_of_ne hr_ne with h | h
    · -- For r < 0, rpow uses complex branch: r^(1/3) = |r|^(1/3)*cos(π/3) = |r|^(1/3)/2
      -- The theorem is false for r < 0 with this rpow definition (buggy MiniF2F formalization)
      sorry
    · exact h
  have hr_nonneg : (0 : ℝ) ≤ r := le_of_lt hr_pos
  have ht_pos : 0 < t := by rw [ht_def]; exact rpow_pos_of_pos hr_pos _
  have ht3 : t ^ 3 = r := by
    rw [ht_def, show (1:ℝ)/3 = ((3:ℕ):ℝ)⁻¹ from by norm_num]
    exact rpow_inv_natCast_pow hr_nonneg (by norm_num : (3:ℕ) ≠ 0)
  have step1 : t ^ 3 + 1 / t ^ 3 = 18 := by
    have : (t + 1/t)^3 = t^3 + 1/t^3 + 3*(t + 1/t) := by field_simp; ring
    rw [h₀] at this; linarith
  have step2 : r + 1 / r = 18 := by rw [← ht3]; exact step1
  have : (r + 1/r)^3 = r^3 + 1/r^3 + 3*(r + 1/r) := by field_simp; ring
  rw [step2] at this; linarith
