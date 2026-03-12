import Mathlib

open BigOperators Real Nat Topology Rat Set

set_option maxHeartbeats 6400000

/-!
# AMC 12A 2020 Problem 9

The equation tan(2x) = cos(x/2) has exactly 5 solutions in [0, 2π].

On [0, 2π], tan(2x) has asymptotes at x = π/4, 3π/4, 5π/4, 7π/4,
creating 5 continuity intervals. On each interval, g(x) = tan(2x) - cos(x/2) is
strictly increasing (its derivative is 2/cos²(2x) + sin(x/2)/2 > 0). By IVT,
there is exactly one zero per interval, giving exactly 5 solutions.
-/

-- ===== Basic helpers =====

private lemma tan_eq_zero_of_cos_eq_zero {x : ℝ} (h : Real.cos x = 0) :
    Real.tan x = 0 := by
  rw [Real.tan_eq_sin_div_cos, h, div_zero]

private lemma tan_two_pi_div_three : Real.tan (2 * Real.pi / 3) = -Real.sqrt 3 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.tan_pi_sub, Real.tan_pi_div_three]

private lemma sqrt_three_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt_three_gt_one : (1 : ℝ) < Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from by simp]
  exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

private lemma sin_half_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * Real.pi) :
    0 ≤ Real.sin (x / 2) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

-- ===== Continuity of g =====

private lemma continuousOn_g {a b : ℝ}
    (hcos : ∀ x ∈ Icc a b, Real.cos (2 * x) ≠ 0) :
    ContinuousOn (fun x => Real.tan (2 * x) - Real.cos (x / 2)) (Icc a b) := by
  apply ContinuousOn.sub
  · apply ContinuousOn.comp Real.continuousOn_tan (continuousOn_const.mul continuousOn_id)
    intro x hx; exact hcos x hx
  · exact (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousOn

-- ===== IVT helper =====

private lemma ivt_root {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun x => Real.tan (2 * x) - Real.cos (x / 2)) (Icc a b))
    (hfa : Real.tan (2 * a) - Real.cos (a / 2) < 0)
    (hfb : Real.tan (2 * b) - Real.cos (b / 2) > 0) :
    ∃ x ∈ Ioo a b, Real.tan (2 * x) = Real.cos (x / 2) := by
  have hab' : a < b := by
    by_contra h; push_neg at h; have := le_antisymm hab h; subst this; linarith
  obtain ⟨x, hx_mem, hx_eq⟩ := intermediate_value_Icc hab hcont
    (show (0 : ℝ) ∈ Icc _ _ from ⟨by linarith, by linarith⟩)
  exact ⟨x, ⟨lt_of_le_of_ne hx_mem.1 (Ne.symm (by intro heq; subst heq; linarith)),
    lt_of_le_of_ne hx_mem.2 (by intro heq; subst heq; linarith)⟩, by linarith⟩

-- ===== cos(2x) ≠ 0 on IVT sub-intervals =====

private lemma cos_2x_ne_zero_I1 :
    ∀ x ∈ Icc (0 : ℝ) (Real.pi / 6), Real.cos (2 * x) ≠ 0 := by
  intro x ⟨hx0, hx1⟩
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩)

private lemma cos_2x_ne_zero_I2 :
    ∀ x ∈ Icc (Real.pi / 3) (2 * Real.pi / 3), Real.cos (2 * x) ≠ 0 := by
  intro x ⟨hx0, hx1⟩
  exact ne_of_lt (Real.cos_neg_of_pi_div_two_lt_of_lt
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

private lemma cos_2x_ne_zero_I3 :
    ∀ x ∈ Icc (5 * Real.pi / 6) (7 * Real.pi / 6), Real.cos (2 * x) ≠ 0 := by
  intro x ⟨hx0, hx1⟩
  have h_shift : Real.cos (2 * x) = Real.cos (2 * x - 2 * Real.pi) := by
    rw [show 2 * x - 2 * Real.pi = 2 * x + (-1 : ℤ) * (2 * Real.pi) from by push_cast; ring]
    rw [Real.cos_add_int_mul_two_pi]
  rw [h_shift]
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, Real.pi_gt_three],
     by nlinarith [Real.pi_pos, Real.pi_gt_three]⟩)

private lemma cos_2x_ne_zero_I4 :
    ∀ x ∈ Icc (4 * Real.pi / 3) (5 * Real.pi / 3), Real.cos (2 * x) ≠ 0 := by
  intro x ⟨hx0, hx1⟩
  have h_shift : Real.cos (2 * x) = Real.cos (2 * x - 2 * Real.pi) := by
    rw [show 2 * x - 2 * Real.pi = 2 * x + (-1 : ℤ) * (2 * Real.pi) from by push_cast; ring]
    rw [Real.cos_add_int_mul_two_pi]
  rw [h_shift]
  exact ne_of_lt (Real.cos_neg_of_pi_div_two_lt_of_lt
    (by nlinarith [Real.pi_pos, Real.pi_gt_three])
    (by nlinarith [Real.pi_pos, Real.pi_gt_three]))

private lemma cos_2x_ne_zero_I5 :
    ∀ x ∈ Icc (11 * Real.pi / 6) (2 * Real.pi), Real.cos (2 * x) ≠ 0 := by
  intro x ⟨hx0, hx1⟩
  have h_shift : Real.cos (2 * x) = Real.cos (2 * x - 4 * Real.pi) := by
    rw [show 2 * x - 4 * Real.pi = 2 * x + (-2 : ℤ) * (2 * Real.pi) from by push_cast; ring]
    rw [Real.cos_add_int_mul_two_pi]
  rw [h_shift]
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, Real.pi_gt_three], by nlinarith [Real.pi_pos]⟩)

-- ===== Sign evaluations =====

private lemma g_neg_at_zero : Real.tan (2 * 0) - Real.cos (0 / 2) < 0 := by
  simp [Real.tan_zero, Real.cos_zero]

private lemma g_pos_at_pi_div_six :
    Real.tan (2 * (Real.pi / 6)) - Real.cos (Real.pi / 6 / 2) > 0 := by
  rw [show 2 * (Real.pi / 6) = Real.pi / 3 from by ring,
      show Real.pi / 6 / 2 = Real.pi / 12 from by ring, Real.tan_pi_div_three]
  linarith [Real.cos_le_one (Real.pi / 12), sqrt_three_gt_one]

private lemma g_neg_at_pi_div_three :
    Real.tan (2 * (Real.pi / 3)) - Real.cos (Real.pi / 3 / 2) < 0 := by
  rw [show 2 * (Real.pi / 3) = 2 * Real.pi / 3 from by ring,
      show Real.pi / 3 / 2 = Real.pi / 6 from by ring,
      tan_two_pi_div_three, Real.cos_pi_div_six]
  linarith [sqrt_three_pos]

private lemma g_pos_at_two_pi_div_three :
    Real.tan (2 * (2 * Real.pi / 3)) - Real.cos (2 * Real.pi / 3 / 2) > 0 := by
  rw [show 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 from by ring,
      show 2 * Real.pi / 3 / 2 = Real.pi / 3 from by ring]
  rw [show (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi from by ring,
      Real.tan_add_pi, Real.tan_pi_div_three, Real.cos_pi_div_three]
  linarith [sqrt_three_gt_one]

private lemma g_neg_at_five_pi_div_six :
    Real.tan (2 * (5 * Real.pi / 6)) - Real.cos (5 * Real.pi / 6 / 2) < 0 := by
  rw [show 2 * (5 * Real.pi / 6) = 5 * Real.pi / 3 from by ring,
      show 5 * Real.pi / 6 / 2 = 5 * Real.pi / 12 from by ring]
  rw [show (5 : ℝ) * Real.pi / 3 = -(Real.pi / 3) + (2 : ℤ) * Real.pi from by push_cast; ring,
      Real.tan_add_int_mul_pi, Real.tan_neg, Real.tan_pi_div_three]
  linarith [sqrt_three_pos,
    show Real.cos (5 * Real.pi / 12) > 0 from Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos, Real.pi_gt_three],
       by nlinarith [Real.pi_pos, Real.pi_gt_three]⟩]

private lemma g_pos_at_seven_pi_div_six :
    Real.tan (2 * (7 * Real.pi / 6)) - Real.cos (7 * Real.pi / 6 / 2) > 0 := by
  rw [show 2 * (7 * Real.pi / 6) = 7 * Real.pi / 3 from by ring,
      show 7 * Real.pi / 6 / 2 = 7 * Real.pi / 12 from by ring]
  rw [show (7 : ℝ) * Real.pi / 3 = Real.pi / 3 + (2 : ℤ) * Real.pi from by push_cast; ring,
      Real.tan_add_int_mul_pi, Real.tan_pi_div_three]
  have : Real.cos (7 * Real.pi / 12) < 0 := by
    rw [show (7 : ℝ) * Real.pi / 12 = Real.pi - 5 * Real.pi / 12 from by ring, Real.cos_pi_sub]
    linarith [show Real.cos (5 * Real.pi / 12) > 0 from Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos, Real.pi_gt_three],
       by nlinarith [Real.pi_pos, Real.pi_gt_three]⟩]
  linarith [sqrt_three_pos]

private lemma g_neg_at_four_pi_div_three :
    Real.tan (2 * (4 * Real.pi / 3)) - Real.cos (4 * Real.pi / 3 / 2) < 0 := by
  rw [show 2 * (4 * Real.pi / 3) = 8 * Real.pi / 3 from by ring,
      show 4 * Real.pi / 3 / 2 = 2 * Real.pi / 3 from by ring]
  rw [show (8 : ℝ) * Real.pi / 3 = 2 * Real.pi / 3 + (2 : ℤ) * Real.pi from by push_cast; ring,
      Real.tan_add_int_mul_pi, tan_two_pi_div_three]
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  linarith [sqrt_three_gt_one]

private lemma g_pos_at_five_pi_div_three :
    Real.tan (2 * (5 * Real.pi / 3)) - Real.cos (5 * Real.pi / 3 / 2) > 0 := by
  rw [show 2 * (5 * Real.pi / 3) = 10 * Real.pi / 3 from by ring,
      show 5 * Real.pi / 3 / 2 = 5 * Real.pi / 6 from by ring]
  rw [show (10 : ℝ) * Real.pi / 3 = Real.pi / 3 + (3 : ℤ) * Real.pi from by push_cast; ring,
      Real.tan_add_int_mul_pi, Real.tan_pi_div_three]
  rw [show (5 : ℝ) * Real.pi / 6 = Real.pi - Real.pi / 6 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_six]
  linarith [sqrt_three_pos]

private lemma g_neg_at_eleven_pi_div_six :
    Real.tan (2 * (11 * Real.pi / 6)) - Real.cos (11 * Real.pi / 6 / 2) < 0 := by
  rw [show 2 * (11 * Real.pi / 6) = 11 * Real.pi / 3 from by ring,
      show 11 * Real.pi / 6 / 2 = 11 * Real.pi / 12 from by ring]
  rw [show (11 : ℝ) * Real.pi / 3 = 2 * Real.pi / 3 + (3 : ℤ) * Real.pi from by push_cast; ring,
      Real.tan_add_int_mul_pi, tan_two_pi_div_three]
  rw [show (11 : ℝ) * Real.pi / 12 = Real.pi - Real.pi / 12 from by ring, Real.cos_pi_sub]
  linarith [Real.cos_le_one (Real.pi / 12), sqrt_three_gt_one]

private lemma g_pos_at_two_pi :
    Real.tan (2 * (2 * Real.pi)) - Real.cos (2 * Real.pi / 2) > 0 := by
  rw [show 2 * (2 * Real.pi) = 4 * Real.pi from by ring,
      show 2 * Real.pi / 2 = Real.pi from by ring]
  rw [show (4 : ℝ) * Real.pi = 0 + (4 : ℤ) * Real.pi from by push_cast; ring,
      Real.tan_add_int_mul_pi, Real.tan_zero, Real.cos_pi]
  norm_num

-- ===== Five solutions exist (IVT) =====

private lemma solution_I1 :
    ∃ x₁, 0 < x₁ ∧ x₁ < Real.pi / 6 ∧ Real.tan (2 * x₁) = Real.cos (x₁ / 2) := by
  obtain ⟨x, hx, hxeq⟩ := ivt_root (by linarith [Real.pi_pos])
    (continuousOn_g cos_2x_ne_zero_I1) g_neg_at_zero g_pos_at_pi_div_six
  exact ⟨x, hx.1, hx.2, hxeq⟩

private lemma solution_I2 :
    ∃ x₂, Real.pi / 3 < x₂ ∧ x₂ < 2 * Real.pi / 3 ∧ Real.tan (2 * x₂) = Real.cos (x₂ / 2) := by
  obtain ⟨x, hx, hxeq⟩ := ivt_root (by nlinarith [Real.pi_pos])
    (continuousOn_g cos_2x_ne_zero_I2) g_neg_at_pi_div_three g_pos_at_two_pi_div_three
  exact ⟨x, hx.1, hx.2, hxeq⟩

private lemma solution_I3 :
    ∃ x₃, 5 * Real.pi / 6 < x₃ ∧ x₃ < 7 * Real.pi / 6 ∧ Real.tan (2 * x₃) = Real.cos (x₃ / 2) := by
  obtain ⟨x, hx, hxeq⟩ := ivt_root (by nlinarith [Real.pi_pos])
    (continuousOn_g cos_2x_ne_zero_I3) g_neg_at_five_pi_div_six g_pos_at_seven_pi_div_six
  exact ⟨x, hx.1, hx.2, hxeq⟩

private lemma solution_I4 :
    ∃ x₄, 4 * Real.pi / 3 < x₄ ∧ x₄ < 5 * Real.pi / 3 ∧ Real.tan (2 * x₄) = Real.cos (x₄ / 2) := by
  obtain ⟨x, hx, hxeq⟩ := ivt_root (by nlinarith [Real.pi_pos])
    (continuousOn_g cos_2x_ne_zero_I4) g_neg_at_four_pi_div_three g_pos_at_five_pi_div_three
  exact ⟨x, hx.1, hx.2, hxeq⟩

private lemma solution_I5 :
    ∃ x₅, 11 * Real.pi / 6 < x₅ ∧ x₅ < 2 * Real.pi ∧ Real.tan (2 * x₅) = Real.cos (x₅ / 2) := by
  obtain ⟨x, hx, hxeq⟩ := ivt_root (by nlinarith [Real.pi_pos])
    (continuousOn_g cos_2x_ne_zero_I5) g_neg_at_eleven_pi_div_six g_pos_at_two_pi
  exact ⟨x, hx.1, hx.2, hxeq⟩

-- ===== card ≥ 5 =====

private lemma card_ge_five (S : Finset ℝ)
    (h₀ : ∀ x : ℝ, x ∈ S ↔ 0 ≤ x ∧ x ≤ 2 * Real.pi ∧ Real.tan (2 * x) = Real.cos (x / 2)) :
    5 ≤ S.card := by
  obtain ⟨x₁, h1a, h1b, h1c⟩ := solution_I1
  obtain ⟨x₂, h2a, h2b, h2c⟩ := solution_I2
  obtain ⟨x₃, h3a, h3b, h3c⟩ := solution_I3
  obtain ⟨x₄, h4a, h4b, h4c⟩ := solution_I4
  obtain ⟨x₅, h5a, h5b, h5c⟩ := solution_I5
  have hm1 : x₁ ∈ S := (h₀ x₁).mpr ⟨by linarith, by nlinarith [Real.pi_pos], h1c⟩
  have hm2 : x₂ ∈ S := (h₀ x₂).mpr ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos], h2c⟩
  have hm3 : x₃ ∈ S := (h₀ x₃).mpr ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos], h3c⟩
  have hm4 : x₄ ∈ S := (h₀ x₄).mpr ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos], h4c⟩
  have hm5 : x₅ ∈ S := (h₀ x₅).mpr ⟨by nlinarith [Real.pi_pos], by linarith, h5c⟩
  have hd12 : x₁ ≠ x₂ := by nlinarith [Real.pi_pos]
  have hd13 : x₁ ≠ x₃ := by nlinarith [Real.pi_pos]
  have hd14 : x₁ ≠ x₄ := by nlinarith [Real.pi_pos]
  have hd15 : x₁ ≠ x₅ := by nlinarith [Real.pi_pos]
  have hd23 : x₂ ≠ x₃ := by nlinarith [Real.pi_pos]
  have hd24 : x₂ ≠ x₄ := by nlinarith [Real.pi_pos]
  have hd25 : x₂ ≠ x₅ := by nlinarith [Real.pi_pos]
  have hd34 : x₃ ≠ x₄ := by nlinarith [Real.pi_pos]
  have hd35 : x₃ ≠ x₅ := by nlinarith [Real.pi_pos]
  have hd45 : x₄ ≠ x₅ := by nlinarith [Real.pi_pos]
  calc 5 = ({x₁, x₂, x₃, x₄, x₅} : Finset ℝ).card := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_singleton]
        · simp [hd45]
        · simp [hd34, hd35]
        · simp [hd23, hd24, hd25]
        · simp [hd12, hd13, hd14, hd15]
    _ ≤ S.card := Finset.card_le_card (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption)

-- ===== Strict monotonicity of g =====

private lemma g_strictMono {a b : ℝ} (_hab : a < b)
    (hcos : ∀ x ∈ Icc a b, Real.cos (2 * x) ≠ 0)
    (hsin : ∀ x ∈ Icc a b, 0 ≤ Real.sin (x / 2)) :
    StrictMonoOn (fun x => Real.tan (2 * x) - Real.cos (x / 2)) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) (continuousOn_g hcos)
  intro x hx
  rw [interior_Icc] at hx
  have hx_icc : x ∈ Icc a b := Ioo_subset_Icc_self hx
  have hcos_ne := hcos x hx_icc
  have hd : HasDerivAt (fun x => Real.tan (2 * x) - Real.cos (x / 2))
      (2 / Real.cos (2 * x) ^ 2 + Real.sin (x / 2) / 2) x := by
    have ht : HasDerivAt (fun x => Real.tan (2 * x)) (2 / Real.cos (2 * x) ^ 2) x := by
      have h := HasDerivAt.comp x (Real.hasDerivAt_tan hcos_ne) (hasDerivAt_id x |>.const_mul 2)
      simp only [Function.comp_def, one_div] at h; convert h using 1; ring
    have hc : HasDerivAt (fun x => Real.cos (x / 2)) (-(Real.sin (x / 2) / 2)) x := by
      have h := HasDerivAt.comp x (Real.hasDerivAt_cos (x / 2)) (hasDerivAt_id x |>.div_const 2)
      simp only [Function.comp_def] at h; convert h using 1; ring
    convert ht.sub hc using 1; ring
  rw [hd.deriv]
  linarith [show 0 < 2 / Real.cos (2 * x) ^ 2 from by positivity,
            show 0 ≤ Real.sin (x / 2) / 2 from div_nonneg (hsin x hx_icc) (by norm_num)]

-- ===== cos(2x) ≠ 0 on each gap =====

private lemma cos2_ne_gap0 {z : ℝ} (h0 : 0 ≤ z) (h1 : z < Real.pi / 4) :
    Real.cos (2 * z) ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by nlinarith [Real.pi_pos]⟩)

private lemma cos2_ne_gap1 {z : ℝ} (h0 : Real.pi / 4 < z) (h1 : z < 3 * Real.pi / 4) :
    Real.cos (2 * z) ≠ 0 :=
  ne_of_lt (Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith) (by nlinarith [Real.pi_pos]))

private lemma cos2_ne_gap2 {z : ℝ} (h0 : 3 * Real.pi / 4 < z) (h1 : z < 5 * Real.pi / 4) :
    Real.cos (2 * z) ≠ 0 := by
  have h_eq : Real.cos (2 * z) = Real.cos (2 * z - 2 * Real.pi) := by
    conv_lhs => rw [show 2 * z = (2 * z - 2 * Real.pi) + (1 : ℤ) * (2 * Real.pi) from by
      push_cast; ring]
    rw [Real.cos_add_int_mul_two_pi]
  rw [h_eq]
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, Real.pi_gt_three],
     by nlinarith [Real.pi_pos, Real.pi_gt_three]⟩)

private lemma cos2_ne_gap3 {z : ℝ} (h0 : 5 * Real.pi / 4 < z) (h1 : z < 7 * Real.pi / 4) :
    Real.cos (2 * z) ≠ 0 := by
  have h_eq : Real.cos (2 * z) = Real.cos (2 * z - 2 * Real.pi) := by
    conv_lhs => rw [show 2 * z = (2 * z - 2 * Real.pi) + (1 : ℤ) * (2 * Real.pi) from by
      push_cast; ring]
    rw [Real.cos_add_int_mul_two_pi]
  rw [h_eq]
  exact ne_of_lt (Real.cos_neg_of_pi_div_two_lt_of_lt
    (by nlinarith [Real.pi_pos, Real.pi_gt_three])
    (by nlinarith [Real.pi_pos, Real.pi_gt_three]))

private lemma cos2_ne_gap4 {z : ℝ} (h0 : 7 * Real.pi / 4 < z) (h1 : z ≤ 2 * Real.pi) :
    Real.cos (2 * z) ≠ 0 := by
  have h_eq : Real.cos (2 * z) = Real.cos (2 * z - 4 * Real.pi) := by
    conv_lhs => rw [show 2 * z = (2 * z - 4 * Real.pi) + (2 : ℤ) * (2 * Real.pi) from by
      push_cast; ring]
    rw [Real.cos_add_int_mul_two_pi]
  rw [h_eq]
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, Real.pi_gt_three], by nlinarith [Real.pi_pos]⟩)

-- ===== Solutions avoid asymptotes =====

private lemma not_sol_pi4 :
    ¬(Real.tan (2 * (Real.pi / 4)) = Real.cos (Real.pi / 4 / 2)) := by
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 from by ring,
      show Real.pi / 4 / 2 = Real.pi / 8 from by ring,
      tan_eq_zero_of_cos_eq_zero Real.cos_pi_div_two]
  linarith [show Real.cos (Real.pi / 8) > 0 from Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, Real.pi_gt_three]⟩]

private lemma not_sol_3pi4 :
    ¬(Real.tan (2 * (3 * Real.pi / 4)) = Real.cos (3 * Real.pi / 4 / 2)) := by
  rw [show 2 * (3 * Real.pi / 4) = 3 * Real.pi / 2 from by ring,
      show 3 * Real.pi / 4 / 2 = 3 * Real.pi / 8 from by ring]
  rw [tan_eq_zero_of_cos_eq_zero (by
    rw [show (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi from by ring,
        Real.cos_add_pi, Real.cos_pi_div_two]; simp)]
  linarith [show Real.cos (3 * Real.pi / 8) > 0 from Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, Real.pi_gt_three]⟩]

private lemma not_sol_5pi4 :
    ¬(Real.tan (2 * (5 * Real.pi / 4)) = Real.cos (5 * Real.pi / 4 / 2)) := by
  rw [show 2 * (5 * Real.pi / 4) = 5 * Real.pi / 2 from by ring,
      show 5 * Real.pi / 4 / 2 = 5 * Real.pi / 8 from by ring]
  rw [tan_eq_zero_of_cos_eq_zero (by
    rw [show (5 : ℝ) * Real.pi / 2 = Real.pi / 2 + (1 : ℤ) * (2 * Real.pi) from by
      push_cast; ring, Real.cos_add_int_mul_two_pi]; exact Real.cos_pi_div_two)]
  have : Real.cos (5 * Real.pi / 8) < 0 := by
    rw [show (5 : ℝ) * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 from by ring, Real.cos_pi_sub]
    linarith [show Real.cos (3 * Real.pi / 8) > 0 from Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, Real.pi_gt_three]⟩]
  linarith

private lemma not_sol_7pi4 :
    ¬(Real.tan (2 * (7 * Real.pi / 4)) = Real.cos (7 * Real.pi / 4 / 2)) := by
  rw [show 2 * (7 * Real.pi / 4) = 7 * Real.pi / 2 from by ring,
      show 7 * Real.pi / 4 / 2 = 7 * Real.pi / 8 from by ring]
  rw [tan_eq_zero_of_cos_eq_zero (by
    rw [show (7 : ℝ) * Real.pi / 2 = -(Real.pi / 2) + (2 : ℤ) * (2 * Real.pi) from by
      push_cast; ring, Real.cos_add_int_mul_two_pi, Real.cos_neg]; exact Real.cos_pi_div_two)]
  have : Real.cos (7 * Real.pi / 8) < 0 := by
    rw [show (7 : ℝ) * Real.pi / 8 = Real.pi - Real.pi / 8 from by ring, Real.cos_pi_sub]
    linarith [show Real.cos (Real.pi / 8) > 0 from Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, Real.pi_gt_three]⟩]
  linarith

-- ===== card ≤ 5 via injection into Fin 5 =====

private noncomputable def gapIdx (x : ℝ) : Fin 5 :=
  if x < Real.pi / 4 then 0
  else if x < 3 * Real.pi / 4 then 1
  else if x < 5 * Real.pi / 4 then 2
  else if x < 7 * Real.pi / 4 then 3
  else 4

-- Two distinct solutions in the same gap contradict strict monotonicity
private lemma same_gap_lt_false {x y : ℝ} (hlt : x < y)
    (hx0 : 0 ≤ x) (_hx1 : x ≤ 2 * Real.pi) (hxeq : Real.tan (2 * x) = Real.cos (x / 2))
    (_hy0 : 0 ≤ y) (hy1 : y ≤ 2 * Real.pi) (hyeq : Real.tan (2 * y) = Real.cos (y / 2))
    (hgap : gapIdx x = gapIdx y) : False := by
  -- First show cos(2z) ≠ 0 for z ∈ [x, y] (they're in the same gap)
  have hx_ne := fun h : x = Real.pi / 4 => not_sol_pi4 (h ▸ hxeq)
  have hx_ne' := fun h : x = 3 * Real.pi / 4 => not_sol_3pi4 (h ▸ hxeq)
  have hx_ne'' := fun h : x = 5 * Real.pi / 4 => not_sol_5pi4 (h ▸ hxeq)
  have hx_ne''' := fun h : x = 7 * Real.pi / 4 => not_sol_7pi4 (h ▸ hxeq)
  have hy_ne := fun h : y = Real.pi / 4 => not_sol_pi4 (h ▸ hyeq)
  have hy_ne' := fun h : y = 3 * Real.pi / 4 => not_sol_3pi4 (h ▸ hyeq)
  have hy_ne'' := fun h : y = 5 * Real.pi / 4 => not_sol_5pi4 (h ▸ hyeq)
  have hy_ne''' := fun h : y = 7 * Real.pi / 4 => not_sol_7pi4 (h ▸ hyeq)
  unfold gapIdx at hgap
  -- The monotonicity argument: g(x) = 0 = g(y) but g is strictly increasing, so x < y → g(x) < g(y)
  suffices hc : ∀ z ∈ Icc x y, Real.cos (2 * z) ≠ 0 by
    have hmono := g_strictMono hlt hc
      (fun z ⟨hz0, hz1⟩ => sin_half_nonneg (by linarith) (by linarith))
    linarith [(hmono.lt_iff_lt ⟨le_refl x, le_of_lt hlt⟩ ⟨le_of_lt hlt, le_refl y⟩).mpr hlt,
              show (fun z => Real.tan (2 * z) - Real.cos (z / 2)) x = 0 from by simp [hxeq],
              show (fun z => Real.tan (2 * z) - Real.cos (z / 2)) y = 0 from by simp [hyeq]]
  -- Case analysis on which gap: split all ifs and handle each case
  split_ifs at hgap with h1 h2 h3 h4 h5 h6 h7 h8
  all_goals first
    | exact absurd hgap (by decide)
    | (have hx_lb : Real.pi / 4 < x := lt_of_le_of_ne (by linarith) (Ne.symm hx_ne)
       exact fun z ⟨hz0, hz1⟩ => cos2_ne_gap1 (by linarith) (by linarith))
    | exact fun z ⟨hz0, hz1⟩ => cos2_ne_gap0 (by linarith) (by linarith)
    | (have hx_lb : 3 * Real.pi / 4 < x := lt_of_le_of_ne (by linarith) (Ne.symm hx_ne')
       exact fun z ⟨hz0, hz1⟩ => cos2_ne_gap2 (by linarith) (by linarith))
    | (have hx_lb : 5 * Real.pi / 4 < x := lt_of_le_of_ne (by linarith) (Ne.symm hx_ne'')
       exact fun z ⟨hz0, hz1⟩ => cos2_ne_gap3 (by linarith) (by linarith))
    | (have hx_lb : 7 * Real.pi / 4 < x := lt_of_le_of_ne (by linarith) (Ne.symm hx_ne''')
       exact fun z ⟨hz0, hz1⟩ => cos2_ne_gap4 (by linarith) (by linarith))

private lemma gapIdx_injOn (S : Finset ℝ)
    (h₀ : ∀ x : ℝ, x ∈ S ↔ 0 ≤ x ∧ x ≤ 2 * Real.pi ∧ Real.tan (2 * x) = Real.cos (x / 2)) :
    Set.InjOn gapIdx ↑S := by
  intro x hx y hy hgap
  rw [Finset.mem_coe] at hx hy
  obtain ⟨hx0, hx1, hxeq⟩ := (h₀ x).mp hx
  obtain ⟨hy0, hy1, hyeq⟩ := (h₀ y).mp hy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · exact (same_gap_lt_false hlt hx0 hx1 hxeq hy0 hy1 hyeq hgap).elim
  · rfl
  · exact (same_gap_lt_false hgt hy0 hy1 hyeq hx0 hx1 hxeq hgap.symm).elim

private lemma card_le_five (S : Finset ℝ)
    (h₀ : ∀ x : ℝ, x ∈ S ↔ 0 ≤ x ∧ x ≤ 2 * Real.pi ∧ Real.tan (2 * x) = Real.cos (x / 2)) :
    S.card ≤ 5 := by
  calc S.card = (S.image gapIdx).card :=
        (Finset.card_image_of_injOn (gapIdx_injOn S h₀)).symm
    _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 5 := by simp

-- ===== Main theorem =====

theorem amc12a_2020_p9
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ 0 ≤ x ∧ x ≤ 2 * Real.pi ∧ Real.tan (2 * x) = Real.cos (x / 2)) :
  S.card = 5 :=
  le_antisymm (card_le_five S h₀) (card_ge_five S h₀)
