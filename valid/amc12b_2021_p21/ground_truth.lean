import Mathlib

open BigOperators Real Nat Topology Rat

-- Helper: positive constant times strictly concave is strictly concave
private lemma strictConcaveOn_const_mul {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ s f)
    {c : ℝ} (hc : 0 < c) : StrictConcaveOn ℝ s (fun x => c * f x) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simp only [smul_eq_mul]
    have := hf.2 hx hy hxy ha hb hab; simp only [smul_eq_mul] at this; nlinarith⟩

-- Helper: positive constant times strictly convex is strictly convex
private lemma strictConvexOn_const_mul {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    {c : ℝ} (hc : 0 < c) : StrictConvexOn ℝ s (fun x => c * f x) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simp only [smul_eq_mul]
    have := hf.2 hx hy hxy ha hb hab; simp only [smul_eq_mul] at this; nlinarith⟩

-- 2^x is strictly convex on (0, ∞)
private lemma strictConvexOn_rpow_two : StrictConvexOn ℝ (Set.Ioi (0:ℝ)) (fun x : ℝ => (2:ℝ) ^ x) := by
  have h : ∀ x : ℝ, (2:ℝ) ^ x = Real.exp (Real.log 2 * x) := fun x =>
    rpow_def_of_pos (by norm_num : (0:ℝ) < 2) x
  refine ⟨convex_Ioi 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, h]
  have hlog2_ne : Real.log 2 ≠ 0 := by positivity
  have key : StrictConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (Real.log 2 * x)) :=
    ⟨convex_univ, fun x _ y _ hxy t s ht hs hts => by
      simp only [smul_eq_mul]
      have := strictConvexOn_exp.2 (Set.mem_univ (Real.log 2 * x)) (Set.mem_univ (Real.log 2 * y))
        (fun h => hxy (mul_left_cancel₀ hlog2_ne h)) ht hs hts
      simp only [smul_eq_mul] at this; convert this using 1; ring_nf⟩
  exact key.2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb hab

-- h(x) = (2^√2)*log(x) - log(√2)*2^x is strictly concave on (0, ∞)
private lemma h_strictConcave :
    StrictConcaveOn ℝ (Set.Ioi (0:ℝ))
      (fun x => (2:ℝ) ^ Real.sqrt 2 * Real.log x - Real.log (Real.sqrt 2) * (2:ℝ) ^ x) := by
  have sqrt2_gt1 : (1:ℝ) < Real.sqrt 2 := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact (strictConcaveOn_const_mul strictConcaveOn_log_Ioi
    (rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)).sub
    (strictConvexOn_const_mul strictConvexOn_rpow_two (Real.log_pos sqrt2_gt1))

-- The equation is equivalent to h(x) = 0 for x > 0
private lemma eq_iff_h_eq_zero (x : ℝ) (hx : 0 < x) :
    x ^ (2:ℝ) ^ Real.sqrt 2 = Real.sqrt 2 ^ (2:ℝ) ^ x ↔
    (2:ℝ) ^ Real.sqrt 2 * Real.log x - Real.log (Real.sqrt 2) * (2:ℝ) ^ x = 0 := by
  have hsqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  rw [sub_eq_zero, show Real.log (Real.sqrt 2) * (2:ℝ) ^ x = (2:ℝ) ^ x * Real.log (Real.sqrt 2) from mul_comm _ _]
  constructor
  · intro h
    have := congr_arg Real.log h
    rwa [Real.log_rpow hx, Real.log_rpow hsqrt2_pos] at this
  · intro h
    have h1 : Real.log (x ^ (2:ℝ) ^ Real.sqrt 2) = Real.log (Real.sqrt 2 ^ (2:ℝ) ^ x) := by
      rw [Real.log_rpow hx, Real.log_rpow hsqrt2_pos]; exact h
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (rpow_pos_of_pos hx _))
      (Set.mem_Ioi.mpr (rpow_pos_of_pos hsqrt2_pos _)) h1

set_option maxHeartbeats 12800000 in
theorem amc12b_2021_p21 (S : Finset ℝ)
  (h₀ : ∀ x : ℝ, x ∈ S ↔ 0 < x ∧ x ^ (2 : ℝ) ^ Real.sqrt 2 = Real.sqrt 2 ^ (2 : ℝ) ^ x) :
  (↑2 ≤ ∑ k ∈ S, k) ∧ (∑ k ∈ S, k) < 6 := by
  -- Every element of S is positive
  have hS_pos_strict : ∀ x ∈ S, 0 < x := fun x hx => ((h₀ x).mp hx).1
  have hS_pos : ∀ x ∈ S, (0 : ℝ) ≤ x := fun x hx => le_of_lt (hS_pos_strict x hx)
  have hS_eq : ∀ x ∈ S, x ^ (2 : ℝ) ^ Real.sqrt 2 = Real.sqrt 2 ^ (2 : ℝ) ^ x :=
    fun x hx => ((h₀ x).mp hx).2
  -- Key bounds on √2
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_lt2 : Real.sqrt 2 < 2 := by nlinarith [hsqrt2_sq]
  have hsqrt2_gt1 : (1 : ℝ) < Real.sqrt 2 := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- √2 is a solution
  have hsqrt2_mem : Real.sqrt 2 ∈ S := by rw [h₀]; exact ⟨hsqrt2_pos, rfl⟩
  -- √2^16 = 256
  have hsqrt2_pow16 : Real.sqrt 2 ^ 16 = (256 : ℝ) := by
    have h4 : Real.sqrt 2 ^ 4 = 4 := by
      have : Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      rw [this, hsqrt2_sq]; norm_num
    have h8 : Real.sqrt 2 ^ 8 = 16 := by
      have : Real.sqrt 2 ^ 8 = (Real.sqrt 2 ^ 4) ^ 2 := by ring
      rw [this, h4]; norm_num
    have : Real.sqrt 2 ^ 16 = (Real.sqrt 2 ^ 8) ^ 2 := by ring
    rw [this, h8]; norm_num
  -- 2^√2 > 2
  have h_exp_gt2 : (2 : ℝ) < (2 : ℝ) ^ Real.sqrt 2 := by
    conv_lhs => rw [show (2 : ℝ) = 2 ^ (1 : ℝ) from (rpow_one 2).symm]
    exact rpow_lt_rpow_of_exponent_lt (by norm_num) hsqrt2_gt1
  -- 2^√2 < 4
  have h_exp_lt4 : (2 : ℝ) ^ Real.sqrt 2 < 4 := by
    calc (2 : ℝ) ^ Real.sqrt 2
        < 2 ^ (2 : ℝ) := rpow_lt_rpow_of_exponent_lt (by norm_num) hsqrt2_lt2
      _ = 4 := by rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, rpow_natCast]; norm_num
  -- f(2) sign: 2^(2^√2) > √2^4 = 4
  have hf2 : Real.sqrt 2 ^ (2 : ℝ) ^ (2 : ℝ) < (2 : ℝ) ^ (2 : ℝ) ^ Real.sqrt 2 := by
    have hrhs_gt : (4 : ℝ) < (2 : ℝ) ^ (2 : ℝ) ^ Real.sqrt 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) from by
        rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, rpow_natCast]; norm_num]
      exact rpow_lt_rpow_of_exponent_lt (by norm_num) h_exp_gt2
    have hlhs_eq : Real.sqrt 2 ^ (2 : ℝ) ^ (2 : ℝ) = 4 := by
      rw [show (2 : ℝ) ^ (2 : ℝ) = ↑(4 : ℕ) from by
        rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, rpow_natCast]; norm_num]
      rw [rpow_natCast]
      have : Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      rw [this, hsqrt2_sq]; norm_num
    linarith
  -- f(4) sign: 4^(2^√2) < √2^16 = 256
  have hf4 : (4 : ℝ) ^ (2 : ℝ) ^ Real.sqrt 2 < Real.sqrt 2 ^ (2 : ℝ) ^ (4 : ℝ) := by
    have hrhs_eq : Real.sqrt 2 ^ (2 : ℝ) ^ (4 : ℝ) = 256 := by
      rw [show (2 : ℝ) ^ (4 : ℝ) = ↑(16 : ℕ) from by
        rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num,
            show (4 : ℝ) = ↑(4 : ℕ) from by norm_num, rpow_natCast]; norm_num]
      rw [rpow_natCast, hsqrt2_pow16]
    rw [hrhs_eq]
    calc (4 : ℝ) ^ (2 : ℝ) ^ Real.sqrt 2
        < 4 ^ (4 : ℝ) := rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 4) h_exp_lt4
      _ = 256 := by rw [show (4 : ℝ) = ↑(4 : ℕ) from by norm_num, rpow_natCast]; norm_num
  -- IVT: second solution x₂ ∈ (2, 4)
  have hIcc : IsPreconnected (Set.Icc (2 : ℝ) 4) := isPreconnected_Icc
  have hg_cont : ContinuousOn (fun x : ℝ => x ^ (2 : ℝ) ^ Real.sqrt 2) (Set.Icc 2 4) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx; left; simp only [id]; linarith [hx.1]
  have hf_cont : ContinuousOn (fun x : ℝ => Real.sqrt 2 ^ (2 : ℝ) ^ x) (Set.Icc 2 4) := by
    apply ContinuousOn.rpow continuousOn_const
    · apply ContinuousOn.rpow continuousOn_const continuousOn_id
      intro x _; left; norm_num
    · intro x _; left; exact ne_of_gt hsqrt2_pos
  obtain ⟨x₂, hx₂_mem, hx₂_eq⟩ := hIcc.intermediate_value₂
    (⟨le_refl _, by norm_num⟩ : (2:ℝ) ∈ Set.Icc 2 4) (⟨by norm_num, le_refl _⟩ : (4:ℝ) ∈ Set.Icc 2 4)
    hf_cont hg_cont (le_of_lt hf2) (le_of_lt hf4)
  have hx₂_gt2 : 2 < x₂ := by
    by_contra h; push_neg at h
    have : x₂ = 2 := le_antisymm h hx₂_mem.1; subst this; linarith [hf2, hx₂_eq]
  have hx₂_lt4 : x₂ < 4 := by
    by_contra h; push_neg at h
    have : x₂ = 4 := le_antisymm hx₂_mem.2 h; subst this; linarith [hf4, hx₂_eq]
  have hx₂_mem_S : x₂ ∈ S := by rw [h₀]; exact ⟨by linarith, hx₂_eq.symm⟩
  have hx₂_ne : x₂ ≠ Real.sqrt 2 := by intro h; linarith
  -- {√2, x₂} ⊆ S
  have hpair_sub : {Real.sqrt 2, x₂} ⊆ S := by
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl; exact hsqrt2_mem; exact hx₂_mem_S
  -- S has at least 2 elements
  have hcard_ge : 2 ≤ S.card := by
    calc 2 = ({Real.sqrt 2, x₂} : Finset ℝ).card := by
          rw [Finset.card_pair hx₂_ne.symm]
      _ ≤ S.card := Finset.card_le_card hpair_sub
  -- S has at most 2 elements (by strict concavity of h)
  have hcard_le : S.card ≤ 2 := by
    by_contra hge
    push_neg at hge
    -- S.card ≥ 3, so there exist 3 ordered elements
    have h3 : 3 ≤ S.card := by omega
    obtain ⟨T, hTS, hT3⟩ := Finset.exists_subset_card_eq h3
    obtain ⟨a, b, c, hab, hac, hbc, hT⟩ := Finset.card_eq_three.mp hT3
    have ha_S : a ∈ S := hTS (hT ▸ Finset.mem_insert_self a _)
    have hb_S : b ∈ S := hTS (hT ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self b _)))
    have hc_S : c ∈ S := hTS (hT ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self c)))))
    have ha_pos : 0 < a := hS_pos_strict a ha_S
    have hb_pos : 0 < b := hS_pos_strict b hb_S
    have hc_pos : 0 < c := hS_pos_strict c hc_S
    -- Get h(a) = 0, h(b) = 0, h(c) = 0
    have ha_eq : (2:ℝ) ^ Real.sqrt 2 * Real.log a - Real.log (Real.sqrt 2) * (2:ℝ) ^ a = 0 :=
      (eq_iff_h_eq_zero a ha_pos).mp (hS_eq a ha_S)
    have hb_eq : (2:ℝ) ^ Real.sqrt 2 * Real.log b - Real.log (Real.sqrt 2) * (2:ℝ) ^ b = 0 :=
      (eq_iff_h_eq_zero b hb_pos).mp (hS_eq b hb_S)
    have hc_eq : (2:ℝ) ^ Real.sqrt 2 * Real.log c - Real.log (Real.sqrt 2) * (2:ℝ) ^ c = 0 :=
      (eq_iff_h_eq_zero c hc_pos).mp (hS_eq c hc_S)
    -- Sort a, b, c
    set h := (fun x => (2:ℝ) ^ Real.sqrt 2 * Real.log x - Real.log (Real.sqrt 2) * (2:ℝ) ^ x)
    -- Use concavity to derive contradiction
    -- h is strictly concave on (0, ∞), and has 3 zeros at a, b, c
    -- For the middle zero, h should be > 0 (between the outer zeros), contradiction
    have hconc := h_strictConcave
    -- We need 3 ordered elements. Use trichotomy.
    suffices key : ∀ (p q r : ℝ), p ∈ S → q ∈ S → r ∈ S →
        p < q → q < r → False by
      rcases lt_trichotomy a b with h1 | h1 | h1
      · rcases lt_trichotomy b c with h2 | h2 | h2
        · exact key a b c ha_S hb_S hc_S h1 h2       -- a < b < c
        · exact absurd h2 hbc
        · rcases lt_trichotomy a c with h3 | h3 | h3
          · exact key a c b ha_S hc_S hb_S h3 h2     -- a < c < b
          · exact absurd h3 hac
          · exact key c a b hc_S ha_S hb_S h3 h1     -- c < a < b
      · exact absurd h1 hab
      · rcases lt_trichotomy b c with h2 | h2 | h2
        · rcases lt_trichotomy a c with h3 | h3 | h3
          · exact key b a c hb_S ha_S hc_S h1 h3     -- b < a < c
          · exact absurd h3 hac
          · exact key b c a hb_S hc_S ha_S h2 h3     -- b < c < a  (need c < a, have a > c)
        · exact absurd h2 hbc
        · exact key c b a hc_S hb_S ha_S h2 h1       -- c < b < a
    intro p q r hp hq hr hpq hqr
    have hp_pos := hS_pos_strict p hp
    have hq_pos := hS_pos_strict q hq
    have hr_pos := hS_pos_strict r hr
    have hp_zero : h p = 0 := (eq_iff_h_eq_zero p hp_pos).mp (hS_eq p hp)
    have hq_zero : h q = 0 := (eq_iff_h_eq_zero q hq_pos).mp (hS_eq q hq)
    have hr_zero : h r = 0 := (eq_iff_h_eq_zero r hr_pos).mp (hS_eq r hr)
    -- By concavity: q is between p and r, so h(q) > 0. But h(q) = 0. Contradiction.
    have hpr_pos : (0:ℝ) < r - p := by linarith
    have ht_pos : 0 < (r - q) / (r - p) := div_pos (by linarith) hpr_pos
    have hu_pos : 0 < (q - p) / (r - p) := div_pos (by linarith) hpr_pos
    have htu : (r - q) / (r - p) + (q - p) / (r - p) = 1 := by
      field_simp; ring
    have hq_combo : (r - q) / (r - p) * p + (q - p) / (r - p) * r = q := by
      field_simp; ring
    -- Apply concavity: h(t*p + u*r) > t*h(p) + u*h(r)
    -- Since h(p) = 0, h(r) = 0: h(t*p + u*r) > 0
    -- But t*p + u*r = q and h(q) = 0, contradiction
    have key := hconc.2 (Set.mem_Ioi.mpr hp_pos) (Set.mem_Ioi.mpr hr_pos)
      (ne_of_lt (by linarith : p < r)) ht_pos hu_pos htu
    simp only [smul_eq_mul] at key
    -- key : t * h(p) + u * h(r) < h(t*p + u*r)
    -- Replace h(p) and h(r) by 0 in key
    have hp_z : (2:ℝ) ^ Real.sqrt 2 * Real.log p - Real.log (Real.sqrt 2) * (2:ℝ) ^ p = 0 := hp_zero
    have hr_z : (2:ℝ) ^ Real.sqrt 2 * Real.log r - Real.log (Real.sqrt 2) * (2:ℝ) ^ r = 0 := hr_zero
    have hq_z : (2:ℝ) ^ Real.sqrt 2 * Real.log q - Real.log (Real.sqrt 2) * (2:ℝ) ^ q = 0 := hq_zero
    rw [hp_z, hr_z, mul_zero, mul_zero, add_zero, hq_combo] at key
    linarith
  -- S.card = 2
  have hcard : S.card = 2 := le_antisymm hcard_le hcard_ge
  -- S = {√2, x₂}
  have hS_eq_pair : S = {Real.sqrt 2, x₂} := by
    obtain ⟨a, b, hab, hS_val⟩ := Finset.card_eq_two.mp hcard
    have hmem1 : Real.sqrt 2 ∈ ({a, b} : Finset ℝ) := hS_val ▸ hsqrt2_mem
    have hmem2 : x₂ ∈ ({a, b} : Finset ℝ) := hS_val ▸ hx₂_mem_S
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
    rw [hS_val]
    rcases hmem1 with rfl | rfl
    · rcases hmem2 with rfl | rfl
      · exact absurd rfl hx₂_ne
      · rfl
    · rcases hmem2 with rfl | rfl
      · rw [Finset.pair_comm]
      · exact absurd rfl hx₂_ne
  -- Compute the sum
  have hne : Real.sqrt 2 ≠ x₂ := hx₂_ne.symm
  rw [hS_eq_pair, Finset.sum_pair hne]
  constructor
  · linarith
  · linarith
