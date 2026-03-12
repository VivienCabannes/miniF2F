import Mathlib

open BigOperators Real Nat Topology Rat Polynomial

set_option maxHeartbeats 6400000

-- Helper: f(x) = 1 - 3 sin x + 5 cos(3x)
noncomputable def f_trig (x : ℝ) : ℝ := 1 - 3 * Real.sin x + 5 * Real.cos (3 * x)

-- f is continuous
lemma f_trig_continuous : Continuous f_trig := by
  unfold f_trig; fun_prop

-- ============================================================
-- Exact evaluations of f at key multiples of π
-- ============================================================

lemma f_trig_zero : f_trig 0 = 6 := by
  unfold f_trig; simp [Real.sin_zero, Real.cos_zero]; ring

lemma f_trig_pi_div_6 : f_trig (Real.pi / 6) = -1/2 := by
  unfold f_trig
  rw [Real.sin_pi_div_six,
      show 3 * (Real.pi / 6) = Real.pi / 2 from by ring, Real.cos_pi_div_two]; ring

lemma f_trig_pi_div_2 : f_trig (Real.pi / 2) = -2 := by
  unfold f_trig
  rw [Real.sin_pi_div_two,
      show 3 * (Real.pi / 2) = Real.pi + Real.pi / 2 from by ring,
      Real.cos_add_pi_div_two, Real.sin_pi]; ring

lemma f_trig_3pi_div_4 : f_trig (3 * Real.pi / 4) = 1 + Real.sqrt 2 := by
  unfold f_trig
  have h1 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 from by ring]
    rw [Real.sin_pi_sub, Real.sin_pi_div_four]
  have h2 : Real.cos (3 * (3 * Real.pi / 4)) = Real.sqrt 2 / 2 := by
    rw [show 3 * (3 * Real.pi / 4) = Real.pi / 4 + 2 * Real.pi from by ring]
    rw [Real.cos_add_two_pi, Real.cos_pi_div_four]
  rw [h1, h2]; ring

lemma f_trig_5pi_div_6 : f_trig (5 * Real.pi / 6) = -1/2 := by
  unfold f_trig
  have h1 : Real.sin (5 * Real.pi / 6) = 1/2 := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 from by ring]
    rw [Real.sin_pi_sub, Real.sin_pi_div_six]
  have h2 : Real.cos (3 * (5 * Real.pi / 6)) = 0 := by
    rw [show 3 * (5 * Real.pi / 6) = Real.pi / 2 + 2 * Real.pi from by ring]
    rw [Real.cos_add_two_pi, Real.cos_pi_div_two]
  rw [h1, h2]; ring

lemma f_trig_pi : f_trig Real.pi = -4 := by
  unfold f_trig
  rw [Real.sin_pi,
      show (3 : ℝ) * Real.pi = Real.pi + 2 * Real.pi from by ring,
      Real.cos_add_two_pi, Real.cos_pi]; ring

lemma f_trig_7pi_div_6 : f_trig (7 * Real.pi / 6) = 5/2 := by
  unfold f_trig
  have h1 : Real.sin (7 * Real.pi / 6) = -(1/2) := by
    rw [show 7 * Real.pi / 6 = Real.pi / 6 + Real.pi from by ring]
    rw [Real.sin_add_pi, Real.sin_pi_div_six]
  have h2 : Real.cos (3 * (7 * Real.pi / 6)) = 0 := by
    rw [show 3 * (7 * Real.pi / 6) = (Real.pi + Real.pi / 2) + 2 * Real.pi from by ring]
    rw [Real.cos_add_two_pi, Real.cos_add_pi_div_two, Real.sin_pi]; simp
  rw [h1, h2]; ring

lemma f_trig_5pi_div_3 : f_trig (5 * Real.pi / 3) = -4 + 3 * Real.sqrt 3 / 2 := by
  unfold f_trig
  have h1 : Real.sin (5 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    rw [show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 from by ring]
    rw [Real.sin_two_pi_sub, Real.sin_pi_div_three]
  have h2 : Real.cos (3 * (5 * Real.pi / 3)) = -1 := by
    rw [show 3 * (5 * Real.pi / 3) = Real.pi + 2 * Real.pi + 2 * Real.pi from by ring]
    rw [show Real.pi + 2 * Real.pi + 2 * Real.pi =
        (Real.pi + 2 * Real.pi) + 2 * Real.pi from by ring]
    rw [Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_pi]
  rw [h1, h2]; ring

lemma f_trig_7pi_div_4 : f_trig (7 * Real.pi / 4) = 1 - Real.sqrt 2 := by
  unfold f_trig
  have h1 : Real.sin (7 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show 7 * Real.pi / 4 = 2 * Real.pi - Real.pi / 4 from by ring]
    rw [Real.sin_two_pi_sub, Real.sin_pi_div_four]
  have h2 : Real.cos (3 * (7 * Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * (7 * Real.pi / 4) = (Real.pi / 4 + Real.pi) + 2 * Real.pi + 2 * Real.pi from by ring]
    rw [show (Real.pi / 4 + Real.pi) + 2 * Real.pi + 2 * Real.pi =
        ((Real.pi / 4 + Real.pi) + 2 * Real.pi) + 2 * Real.pi from by ring]
    rw [Real.cos_add_two_pi]
    rw [show (Real.pi / 4 + Real.pi) + 2 * Real.pi = (Real.pi / 4 + Real.pi) + 2 * Real.pi from rfl]
    rw [Real.cos_add_two_pi, Real.cos_add_pi, Real.cos_pi_div_four]
  rw [h1, h2]; ring

lemma f_trig_11pi_div_6 : f_trig (11 * Real.pi / 6) = 5/2 := by
  unfold f_trig
  have h1 : Real.sin (11 * Real.pi / 6) = -(1/2) := by
    rw [show 11 * Real.pi / 6 = 2 * Real.pi - Real.pi / 6 from by ring]
    rw [Real.sin_two_pi_sub, Real.sin_pi_div_six]
  have h2 : Real.cos (3 * (11 * Real.pi / 6)) = 0 := by
    rw [show 3 * (11 * Real.pi / 6) = (Real.pi / 2 + Real.pi) + 2 * Real.pi + 2 * Real.pi from by ring]
    rw [show (Real.pi / 2 + Real.pi) + 2 * Real.pi + 2 * Real.pi =
        ((Real.pi / 2 + Real.pi) + 2 * Real.pi) + 2 * Real.pi from by ring]
    rw [Real.cos_add_two_pi]
    rw [show (Real.pi / 2 + Real.pi) + 2 * Real.pi = (Real.pi / 2 + Real.pi) + 2 * Real.pi from rfl]
    rw [Real.cos_add_two_pi, Real.cos_add_pi, Real.cos_pi_div_two]; simp
  rw [h1, h2]; ring

-- ============================================================
-- Sign lemmas (positivity / negativity)
-- ============================================================

lemma f_trig_zero_pos : 0 < f_trig 0 := by rw [f_trig_zero]; norm_num
lemma f_trig_pi_div_6_neg : f_trig (Real.pi / 6) < 0 := by rw [f_trig_pi_div_6]; norm_num
lemma f_trig_pi_div_2_neg : f_trig (Real.pi / 2) < 0 := by rw [f_trig_pi_div_2]; norm_num
lemma f_trig_5pi_div_6_neg : f_trig (5 * Real.pi / 6) < 0 := by rw [f_trig_5pi_div_6]; norm_num
lemma f_trig_pi_neg : f_trig Real.pi < 0 := by rw [f_trig_pi]; norm_num
lemma f_trig_7pi_div_6_pos : 0 < f_trig (7 * Real.pi / 6) := by rw [f_trig_7pi_div_6]; norm_num
lemma f_trig_11pi_div_6_pos : 0 < f_trig (11 * Real.pi / 6) := by rw [f_trig_11pi_div_6]; norm_num

lemma f_trig_3pi_div_4_pos : 0 < f_trig (3 * Real.pi / 4) := by
  rw [f_trig_3pi_div_4]; linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]

lemma f_trig_7pi_div_4_neg : f_trig (7 * Real.pi / 4) < 0 := by
  rw [f_trig_7pi_div_4]
  have h : Real.sqrt 2 > 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma f_trig_5pi_div_3_neg : f_trig (5 * Real.pi / 3) < 0 := by
  rw [f_trig_5pi_div_3]
  have h1 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
  have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  nlinarith [sq_nonneg (Real.sqrt 3 - 2)]

-- ============================================================
-- Weierstrass substitution and polynomial upper bound
-- ============================================================

-- sin(x) = 2*tan(x/2)/(1+tan(x/2)^2) when cos(x/2) ≠ 0
private lemma sin_weierstrass (x : ℝ) (hc : Real.cos (x / 2) ≠ 0) :
    Real.sin x = 2 * Real.tan (x / 2) / (1 + Real.tan (x / 2) ^ 2) := by
  have h1 : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    conv_lhs => rw [show x = 2 * (x / 2) from by ring]
    exact Real.sin_two_mul (x / 2)
  have h2 : Real.sin (x / 2) = Real.tan (x / 2) * Real.cos (x / 2) := by
    rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hc]
  have h3 : Real.cos (x / 2) ^ 2 = (1 + Real.tan (x / 2) ^ 2)⁻¹ := by
    rw [Real.inv_one_add_tan_sq hc]
  rw [h1, h2]
  set t := Real.tan (x / 2)
  set c := Real.cos (x / 2)
  have : 2 * (t * c) * c = 2 * t * c ^ 2 := by ring
  rw [this, h3, div_eq_mul_inv]

-- cos(x) = (1-tan(x/2)^2)/(1+tan(x/2)^2) when cos(x/2) ≠ 0
private lemma cos_weierstrass (x : ℝ) (hc : Real.cos (x / 2) ≠ 0) :
    Real.cos x = (1 - Real.tan (x / 2) ^ 2) / (1 + Real.tan (x / 2) ^ 2) := by
  have h1 : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    conv_lhs => rw [show x = 2 * (x / 2) from by ring]
    exact Real.cos_two_mul (x / 2)
  have h2 : Real.cos (x / 2) ^ 2 = (1 + Real.tan (x / 2) ^ 2)⁻¹ := by
    rw [Real.inv_one_add_tan_sq hc]
  set t := Real.tan (x / 2)
  rw [h1, h2]; field_simp; ring

-- The key identity: f_trig(x) * (1+tan(x/2)^2)^3 = -2 * p(tan(x/2))
-- where p(t) = 2t^6 + 3t^5 - 39t^4 + 6t^3 + 36t^2 + 3t - 3
private lemma f_trig_weierstrass (x : ℝ) (hc : Real.cos (x / 2) ≠ 0) :
    f_trig x * (1 + Real.tan (x / 2) ^ 2) ^ 3 =
    -(2 * (2 * Real.tan (x / 2) ^ 6 + 3 * Real.tan (x / 2) ^ 5 -
           39 * Real.tan (x / 2) ^ 4 + 6 * Real.tan (x / 2) ^ 3 +
           36 * Real.tan (x / 2) ^ 2 + 3 * Real.tan (x / 2) - 3)) := by
  set t := Real.tan (x / 2) with ht_def
  have hsin : Real.sin x = 2 * t / (1 + t ^ 2) := sin_weierstrass x hc
  have hcos : Real.cos x = (1 - t ^ 2) / (1 + t ^ 2) := cos_weierstrass x hc
  have hcos3 : Real.cos (3 * x) = 4 * (Real.cos x) ^ 3 - 3 * Real.cos x :=
    Real.cos_three_mul x
  unfold f_trig; rw [hcos3, hcos, hsin]; field_simp; ring

-- f_trig(x) = 0 implies the polynomial vanishes at tan(x/2)
private lemma f_trig_zero_imp_poly_zero (x : ℝ) (hc : Real.cos (x / 2) ≠ 0) (hf : f_trig x = 0) :
    2 * Real.tan (x / 2) ^ 6 + 3 * Real.tan (x / 2) ^ 5 -
    39 * Real.tan (x / 2) ^ 4 + 6 * Real.tan (x / 2) ^ 3 +
    36 * Real.tan (x / 2) ^ 2 + 3 * Real.tan (x / 2) - 3 = 0 := by
  have h := f_trig_weierstrass x hc; rw [hf, zero_mul] at h; linarith

-- The degree 6 polynomial from Weierstrass substitution
private noncomputable def weierPoly : ℝ[X] :=
  C 2 * X ^ 6 + C 3 * X ^ 5 + C (-39) * X ^ 4 + C 6 * X ^ 3 + C 36 * X ^ 2 + C 3 * X + C (-3)

private lemma weierPoly_eval (t : ℝ) :
    weierPoly.eval t = 2 * t ^ 6 + 3 * t ^ 5 - 39 * t ^ 4 + 6 * t ^ 3 + 36 * t ^ 2 + 3 * t - 3 := by
  unfold weierPoly; simp [eval_add, eval_mul, eval_pow, eval_C, eval_X]; ring

private lemma weierPoly_ne_zero : weierPoly ≠ 0 := by
  unfold weierPoly; intro h
  have := congr_arg (fun p => Polynomial.coeff p 0) h
  simp [coeff_add, coeff_mul, coeff_C, coeff_X_pow, coeff_X] at this

private lemma weierPoly_natDegree_le : weierPoly.natDegree ≤ 6 := by
  unfold weierPoly; compute_degree!

-- cos(x/2) ≠ 0 for x in (0, 2π) with x ≠ π
private lemma cos_half_ne_zero_of_mem {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 2 * Real.pi)
    (hx_ne : x ≠ Real.pi) : Real.cos (x / 2) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : (0 : ℝ) < (2 * ↑k + 1) := by
    by_contra h_neg; push_neg at h_neg; nlinarith [hk]
  have h2 : (2 * (k : ℝ) + 1) < 2 := by nlinarith [hk]
  have hk_ge : (0 : ℤ) ≤ k := by
    by_contra h; push_neg at h
    have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt (by omega : k < 0)
    linarith
  have hk_le : k ≤ (0 : ℤ) := by
    by_contra h; push_neg at h
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    linarith
  have hk0 : k = 0 := le_antisymm hk_le hk_ge
  subst hk0; simp at hk; exact hx_ne (by linarith)

-- tan(·/2) is injective on (0, 2π) \ {π}
private lemma tan_half_injOn :
    Set.InjOn (fun x => Real.tan (x / 2)) {x : ℝ | 0 < x ∧ x < 2 * Real.pi ∧ x ≠ Real.pi} := by
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  have hcos_a : Real.cos (a / 2) ≠ 0 := cos_half_ne_zero_of_mem ha.1 ha.2.1 ha.2.2
  have hcos_b : Real.cos (b / 2) ≠ 0 := cos_half_ne_zero_of_mem hb.1 hb.2.1 hb.2.2
  have hab' : Real.tan (a / 2) = Real.tan (b / 2) := hab
  have h_sin_diff : Real.sin (a / 2 - b / 2) = 0 := by
    rw [Real.sin_sub]
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos] at hab'
    have := (div_eq_div_iff hcos_a hcos_b).mp hab'
    linarith
  rw [Real.sin_eq_zero_iff] at h_sin_diff
  obtain ⟨n, hn⟩ := h_sin_diff
  have h_ab : a - b = 2 * ↑n * Real.pi := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn_zero : n = 0 := by
    by_contra hne
    rcases show n ≥ 1 ∨ n ≤ -1 from by omega with h1 | h1
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      nlinarith [ha.1, hb.2.1]
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast h1
      nlinarith [hb.1, ha.2.1]
  subst hn_zero; simp at h_ab; linarith

-- ============================================================
-- Main theorem
-- ============================================================

/-
  The equation f(x) = 1 - 3sin(x) + 5cos(3x) = 0 has exactly 6 solutions in (0, 2π].

  LOWER BOUND (≥ 6):
  We have 6 disjoint intervals where f changes sign:
  1. (0, π/6):       f(0) = 6 > 0,       f(π/6) = -1/2 < 0
  2. (π/2, 3π/4):    f(π/2) = -2 < 0,    f(3π/4) = 1+√2 > 0
  3. (3π/4, 5π/6):   f(3π/4) = 1+√2 > 0, f(5π/6) = -1/2 < 0
  4. (π, 7π/6):      f(π) = -4 < 0,      f(7π/6) = 5/2 > 0
  5. (7π/6, 5π/3):   f(7π/6) = 5/2 > 0,  f(5π/3) = -4+3√3/2 < 0
  6. (7π/4, 11π/6):  f(7π/4) = 1-√2 < 0, f(11π/6) = 5/2 > 0
  By IVT, each interval contains at least one zero. Since the intervals are
  disjoint, these give 6 distinct zeros, all in (0, 2π]. So S.card ≥ 6.

  UPPER BOUND (≤ 6):
  The Weierstrass substitution t = tan(x/2) converts f(x) = 0 into:
    2t⁶ + 3t⁵ - 39t⁴ + 6t³ + 36t² + 3t - 3 = 0
  which is a degree 6 polynomial. Since f(π) = -4 ≠ 0 and f(2π) = 6 ≠ 0,
  every solution in (0, 2π] corresponds to a real root of this polynomial.
  A degree 6 polynomial has at most 6 real roots, so S.card ≤ 6.

  All sign evaluations above have been formally verified. The IVT applications
  and polynomial upper bound argument require additional infrastructure that
  is beyond practical formalization scope.
-/
-- IVT helper: if f is continuous on [a,b], f(a) < 0, f(b) > 0, then ∃ c ∈ (a,b), f(c) = 0
lemma ivt_zero_of_neg_pos {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c, c ∈ Set.Ioo a b ∧ f c = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt hfa, le_of_lt hfb⟩
  have := intermediate_value_Icc (le_of_lt hab) hf h0
  obtain ⟨c, hc_mem, hc_val⟩ := this
  by_cases hca : c = a
  · exfalso; rw [hca] at hc_val; linarith
  · by_cases hcb : c = b
    · exfalso; rw [hcb] at hc_val; linarith
    · exact ⟨c, ⟨lt_of_le_of_ne hc_mem.1 (Ne.symm hca),
                  lt_of_le_of_ne hc_mem.2 hcb⟩, hc_val⟩

-- Same but with f(a) > 0, f(b) < 0
lemma ivt_zero_of_pos_neg {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hfa : 0 < f a) (hfb : f b < 0) :
    ∃ c, c ∈ Set.Ioo a b ∧ f c = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨le_of_lt hfb, le_of_lt hfa⟩
  have := intermediate_value_Icc' (le_of_lt hab) hf h0
  obtain ⟨c, hc_mem, hc_val⟩ := this
  by_cases hca : c = a
  · exfalso; rw [hca] at hc_val; linarith
  · by_cases hcb : c = b
    · exfalso; rw [hcb] at hc_val; linarith
    · exact ⟨c, ⟨lt_of_le_of_ne hc_mem.1 (Ne.symm hca),
                  lt_of_le_of_ne hc_mem.2 hcb⟩, hc_val⟩

-- f_trig is continuous on any interval
lemma f_trig_continuousOn (s : Set ℝ) : ContinuousOn f_trig s :=
  f_trig_continuous.continuousOn

-- The 6 disjoint intervals where f_trig changes sign, each giving a root
-- Interval 1: (0, π/6) - f(0) = 6 > 0, f(π/6) = -1/2 < 0
-- Interval 2: (π/2, 3π/4) - f(π/2) = -2 < 0, f(3π/4) = 1+√2 > 0
-- Interval 3: (3π/4, 5π/6) - f(3π/4) = 1+√2 > 0, f(5π/6) = -1/2 < 0
-- Interval 4: (π, 7π/6) - f(π) = -4 < 0, f(7π/6) = 5/2 > 0
-- Interval 5: (7π/6, 5π/3) - f(7π/6) = 5/2 > 0, f(5π/3) = -4+3√3/2 < 0
-- Interval 6: (7π/4, 11π/6) - f(7π/4) = 1-√2 < 0, f(11π/6) = 5/2 > 0

-- Existence of roots in each interval
lemma root_in_interval_1 : ∃ c, c ∈ Set.Ioo 0 (Real.pi / 6) ∧ f_trig c = 0 := by
  apply ivt_zero_of_pos_neg (by positivity)
    (f_trig_continuousOn _) f_trig_zero_pos f_trig_pi_div_6_neg

lemma root_in_interval_2 : ∃ c, c ∈ Set.Ioo (Real.pi / 2) (3 * Real.pi / 4) ∧ f_trig c = 0 := by
  apply ivt_zero_of_neg_pos (by nlinarith [Real.pi_gt_three])
    (f_trig_continuousOn _) f_trig_pi_div_2_neg f_trig_3pi_div_4_pos

lemma root_in_interval_3 : ∃ c, c ∈ Set.Ioo (3 * Real.pi / 4) (5 * Real.pi / 6) ∧ f_trig c = 0 := by
  apply ivt_zero_of_pos_neg (by nlinarith [Real.pi_gt_three])
    (f_trig_continuousOn _) f_trig_3pi_div_4_pos f_trig_5pi_div_6_neg

lemma root_in_interval_4 : ∃ c, c ∈ Set.Ioo Real.pi (7 * Real.pi / 6) ∧ f_trig c = 0 := by
  apply ivt_zero_of_neg_pos (by nlinarith [Real.pi_gt_three])
    (f_trig_continuousOn _) f_trig_pi_neg f_trig_7pi_div_6_pos

lemma root_in_interval_5 : ∃ c, c ∈ Set.Ioo (7 * Real.pi / 6) (5 * Real.pi / 3) ∧ f_trig c = 0 := by
  apply ivt_zero_of_pos_neg (by nlinarith [Real.pi_gt_three])
    (f_trig_continuousOn _) f_trig_7pi_div_6_pos f_trig_5pi_div_3_neg

lemma root_in_interval_6 : ∃ c, c ∈ Set.Ioo (7 * Real.pi / 4) (11 * Real.pi / 6) ∧ f_trig c = 0 := by
  apply ivt_zero_of_neg_pos (by nlinarith [Real.pi_gt_three])
    (f_trig_continuousOn _) f_trig_7pi_div_4_neg f_trig_11pi_div_6_pos

-- The roots are in (0, 2π] and satisfy the equation, hence are in S
lemma root_in_S {S : Finset ℝ}
    (h₀ : ∀ (x : ℝ), x ∈ S ↔ 0 < x ∧ x ≤ 2 * Real.pi ∧ 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0)
    {c : ℝ} (hc_pos : 0 < c) (hc_le : c ≤ 2 * Real.pi) (hc_eq : f_trig c = 0) :
    c ∈ S := by
  rw [h₀]
  refine ⟨hc_pos, hc_le, ?_⟩
  have := hc_eq
  unfold f_trig at this
  linarith

-- Auxiliary: all 6 intervals are contained in (0, 2π]
-- and the intervals are pairwise disjoint

-- Helper to establish membership in S for each root
private lemma mem_S_from_Ioo {S : Finset ℝ}
    (h₀ : ∀ (x : ℝ), x ∈ S ↔ 0 < x ∧ x ≤ 2 * Real.pi ∧ 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 2 * Real.pi)
    {c : ℝ} (hc : c ∈ Set.Ioo a b) (hfc : f_trig c = 0) : c ∈ S :=
  root_in_S h₀ (lt_of_le_of_lt ha hc.1) (le_trans (le_of_lt hc.2) hb) hfc

-- The 6 intervals are ordered: their union is in (0, 11π/6)
-- and they are pairwise disjoint since:
-- (0, π/6) < (π/2, 3π/4) < (3π/4, 5π/6) < (π, 7π/6) < (7π/6, 5π/3) < (7π/4, 11π/6)

theorem amc12b_2021_p13
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ 0 < x ∧ x ≤ 2 * Real.pi ∧ 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0) :
  S.card = 6 := by
  apply le_antisymm
  · -- Upper bound: S.card ≤ 6
    -- Via t = tan(x/2), solutions in (0,2π)\{π} correspond to real roots of
    -- 2t⁶+3t⁵-39t⁴+6t³+36t²+3t-3 = 0 (degree 6, at most 6 real roots).
    -- Since f(π)=-4≠0 and f(2π)=6≠0, all solutions are captured.
    -- Step 1: Every element of S is in (0, 2π), ≠ π, and satisfies f_trig = 0
    have hS_mem : ∀ x ∈ S, 0 < x ∧ x < 2 * Real.pi ∧ x ≠ Real.pi ∧ f_trig x = 0 := by
      intro x hx
      rw [h₀] at hx; obtain ⟨hpos, hle, heq⟩ := hx
      refine ⟨hpos, ?_, ?_, ?_⟩
      · rcases eq_or_lt_of_le hle with rfl | hlt
        · exfalso
          have h1 : Real.sin (2 * Real.pi) = 0 := Real.sin_two_pi
          have h2 : Real.cos (3 * (2 * Real.pi)) = 1 := by
            have : Real.cos (6 * Real.pi) = 1 := by
              rw [show (6 : ℝ) * Real.pi = 0 + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi from by ring]
              simp [Real.cos_add_two_pi]
            rwa [show 3 * (2 * Real.pi) = 6 * Real.pi from by ring]
          linarith [h1, h2]
        · exact hlt
      · intro heq_pi; subst heq_pi
        have h1 : Real.sin Real.pi = 0 := Real.sin_pi
        have h2 : Real.cos (3 * Real.pi) = -1 := by
          rw [show 3 * Real.pi = Real.pi + 2 * Real.pi from by ring,
              Real.cos_add_two_pi, Real.cos_pi]
        linarith [h1, h2]
      · unfold f_trig; linarith
    -- Step 2: For each x ∈ S, tan(x/2) is a root of weierPoly
    have hS_root : ∀ x ∈ S, weierPoly.IsRoot (Real.tan (x / 2)) := by
      intro x hx
      obtain ⟨hpos, hlt, hne, hf⟩ := hS_mem x hx
      rw [Polynomial.IsRoot, weierPoly_eval]
      exact f_trig_zero_imp_poly_zero x (cos_half_ne_zero_of_mem hpos hlt hne) hf
    -- Step 3: tan(·/2) is injective on S
    have hS_inj : Set.InjOn (fun x => Real.tan (x / 2)) (↑S : Set ℝ) := by
      intro a ha b hb hab
      apply tan_half_injOn
      · exact ⟨(hS_mem a ha).1, (hS_mem a ha).2.1, (hS_mem a ha).2.2.1⟩
      · exact ⟨(hS_mem b hb).1, (hS_mem b hb).2.1, (hS_mem b hb).2.2.1⟩
      · exact hab
    -- Step 4: Image lands in roots of weierPoly
    have h_image_sub : (S.image (fun x => Real.tan (x / 2))).val ⊆ weierPoly.roots := by
      intro t ht
      rw [Finset.mem_val, Finset.mem_image] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      exact (Polynomial.mem_roots weierPoly_ne_zero).mpr (hS_root x hx)
    -- Step 5: Conclude S.card ≤ 6
    calc S.card
        = (S.image (fun x => Real.tan (x / 2))).card :=
            (Finset.card_image_of_injOn hS_inj).symm
      _ ≤ Multiset.card weierPoly.roots :=
            Multiset.card_le_card (Finset.val_le_iff_val_subset.mpr h_image_sub)
      _ ≤ weierPoly.natDegree := Polynomial.card_roots' _
      _ ≤ 6 := weierPoly_natDegree_le
  · -- Lower bound: S.card ≥ 6
    -- Get 6 roots from IVT
    obtain ⟨c₁, hc₁_mem, hc₁_eq⟩ := root_in_interval_1
    obtain ⟨c₂, hc₂_mem, hc₂_eq⟩ := root_in_interval_2
    obtain ⟨c₃, hc₃_mem, hc₃_eq⟩ := root_in_interval_3
    obtain ⟨c₄, hc₄_mem, hc₄_eq⟩ := root_in_interval_4
    obtain ⟨c₅, hc₅_mem, hc₅_eq⟩ := root_in_interval_5
    obtain ⟨c₆, hc₆_mem, hc₆_eq⟩ := root_in_interval_6
    -- Show all roots are in S
    have hS₁ : c₁ ∈ S := mem_S_from_Ioo h₀ (le_refl 0)
      (by nlinarith [Real.pi_gt_three]) hc₁_mem hc₁_eq
    have hS₂ : c₂ ∈ S := mem_S_from_Ioo h₀
      (by nlinarith [Real.pi_gt_three]) (by nlinarith [Real.pi_gt_three]) hc₂_mem hc₂_eq
    have hS₃ : c₃ ∈ S := mem_S_from_Ioo h₀
      (by nlinarith [Real.pi_gt_three]) (by nlinarith [Real.pi_gt_three]) hc₃_mem hc₃_eq
    have hS₄ : c₄ ∈ S := mem_S_from_Ioo h₀
      (by nlinarith [Real.pi_gt_three]) (by nlinarith [Real.pi_gt_three]) hc₄_mem hc₄_eq
    have hS₅ : c₅ ∈ S := mem_S_from_Ioo h₀
      (by nlinarith [Real.pi_gt_three]) (by nlinarith [Real.pi_gt_three]) hc₅_mem hc₅_eq
    have hS₆ : c₆ ∈ S := mem_S_from_Ioo h₀
      (by nlinarith [Real.pi_gt_three]) (by nlinarith [Real.pi_gt_three]) hc₆_mem hc₆_eq
    -- Show all roots are distinct (they come from disjoint intervals)
    -- The intervals are ordered: c₁ < π/6 ≤ π/2 < c₂ < 3π/4 = left of interval 3
    -- so c₁ < c₂ < c₃ < c₄ < c₅ < c₆
    have h12 : c₁ ≠ c₂ := by
      intro heq; rw [heq] at hc₁_mem
      have := hc₁_mem.2; have := hc₂_mem.1
      nlinarith [Real.pi_gt_three]
    have h13 : c₁ ≠ c₃ := by
      intro heq; rw [heq] at hc₁_mem
      have := hc₁_mem.2; have := hc₃_mem.1
      nlinarith [Real.pi_gt_three]
    have h14 : c₁ ≠ c₄ := by
      intro heq; rw [heq] at hc₁_mem
      have := hc₁_mem.2; have := hc₄_mem.1
      nlinarith [Real.pi_gt_three]
    have h15 : c₁ ≠ c₅ := by
      intro heq; rw [heq] at hc₁_mem
      have := hc₁_mem.2; have := hc₅_mem.1
      nlinarith [Real.pi_gt_three]
    have h16 : c₁ ≠ c₆ := by
      intro heq; rw [heq] at hc₁_mem
      have := hc₁_mem.2; have := hc₆_mem.1
      nlinarith [Real.pi_gt_three]
    have h23 : c₂ ≠ c₃ := by
      intro heq; rw [heq] at hc₂_mem
      have := hc₂_mem.2; have := hc₃_mem.1
      nlinarith
    have h24 : c₂ ≠ c₄ := by
      intro heq; rw [heq] at hc₂_mem
      have := hc₂_mem.2; have := hc₄_mem.1
      nlinarith [Real.pi_gt_three]
    have h25 : c₂ ≠ c₅ := by
      intro heq; rw [heq] at hc₂_mem
      have := hc₂_mem.2; have := hc₅_mem.1
      nlinarith [Real.pi_gt_three]
    have h26 : c₂ ≠ c₆ := by
      intro heq; rw [heq] at hc₂_mem
      have := hc₂_mem.2; have := hc₆_mem.1
      nlinarith [Real.pi_gt_three]
    have h34 : c₃ ≠ c₄ := by
      intro heq; rw [heq] at hc₃_mem
      have := hc₃_mem.2; have := hc₄_mem.1
      nlinarith [Real.pi_gt_three]
    have h35 : c₃ ≠ c₅ := by
      intro heq; rw [heq] at hc₃_mem
      have := hc₃_mem.2; have := hc₅_mem.1
      nlinarith [Real.pi_gt_three]
    have h36 : c₃ ≠ c₆ := by
      intro heq; rw [heq] at hc₃_mem
      have := hc₃_mem.2; have := hc₆_mem.1
      nlinarith [Real.pi_gt_three]
    have h45 : c₄ ≠ c₅ := by
      intro heq; rw [heq] at hc₄_mem
      have := hc₄_mem.2; have := hc₅_mem.1
      nlinarith
    have h46 : c₄ ≠ c₆ := by
      intro heq; rw [heq] at hc₄_mem
      have := hc₄_mem.2; have := hc₆_mem.1
      nlinarith [Real.pi_gt_three]
    have h56 : c₅ ≠ c₆ := by
      intro heq; rw [heq] at hc₅_mem
      have := hc₅_mem.2; have := hc₆_mem.1
      nlinarith [Real.pi_gt_three]
    -- Now we have 6 distinct elements in S
    -- Use Finset.card_le_card or construct a subset
    have : ({c₁, c₂, c₃, c₄, c₅, c₆} : Finset ℝ).card = 6 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14, h15, h16])]
      rw [Finset.card_insert_of_notMem (by simp [h23, h24, h25, h26])]
      rw [Finset.card_insert_of_notMem (by simp [h34, h35, h36])]
      rw [Finset.card_insert_of_notMem (by simp [h45, h46])]
      rw [Finset.card_insert_of_notMem (by simp [h56])]
      simp
    calc 6 = ({c₁, c₂, c₃, c₄, c₅, c₆} : Finset ℝ).card := this.symm
      _ ≤ S.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hS₁
          · exact hS₂
          · exact hS₃
          · exact hS₄
          · exact hS₅
          · exact hS₆
