import Mathlib

open BigOperators Real Nat Topology Rat Polynomial Complex

set_option maxHeartbeats 25600000

theorem amc12a_2021_p12
  (a b c d : ℝ)
  (f : ℂ → ℂ)
  (h₀ : ∀ z, f z = z^6 - 10 * z^5 + a * z^4 + b * z^3 + c * z^2 + d * z + 16)
  (h₁ : ∀ z, f z = 0 → (z.im = 0 ∧ 0 < z.re ∧ ↑(Int.floor z.re) = z.re)) :
  b = -88 := by
  -- PART A: Reduce to f(z) = (z-1)^2*(z-2)^4
  suffices hf_factor : ∀ z : ℂ, f z = (z - 1) ^ 2 * (z - 2) ^ 4 by
    have key_real : ∀ (x : ℝ),
        x ^ 6 - 10 * x ^ 5 + a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + 16 =
        (x - 1) ^ 2 * (x - 2) ^ 4 := by
      intro x
      have h := hf_factor (↑x); rw [h₀] at h
      apply Complex.ofReal_injective; push_cast
      convert h using 1
    nlinarith [key_real 0, key_real 1, key_real 2, key_real 3, key_real (-1)]
  -- PART B: Prove f(z) = (z-1)^2*(z-2)^4 using FTA
  let p : ℂ[X] := X ^ 6 - C 10 * X ^ 5 + C (↑a : ℂ) * X ^ 4 +
    C (↑b : ℂ) * X ^ 3 + C (↑c : ℂ) * X ^ 2 + C (↑d : ℂ) * X + C 16
  have show_p : p = X ^ 6 - C 10 * X ^ 5 + C (↑a : ℂ) * X ^ 4 +
    C (↑b : ℂ) * X ^ 3 + C (↑c : ℂ) * X ^ 2 + C (↑d : ℂ) * X + C 16 := rfl
  have heval : ∀ z : ℂ, p.eval z = f z := by
    intro z; simp [p, h₀, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  have hp_ne : p ≠ 0 := by
    intro hp0; have : p.eval 0 = 0 := by rw [hp0]; simp
    rw [heval, h₀] at this; norm_num at this
  have hp_monic : p.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one 6
    · rw [show_p]; compute_degree!
    · rw [show_p]
      simp only [coeff_add, coeff_sub, coeff_mul, coeff_X, coeff_C, coeff_X_pow,
        Finset.antidiagonal]
      simp (config := { decide := true })
  have hp_deg : p.natDegree = 6 := by rw [show_p]; compute_degree!
  have hp_splits : p.Splits (RingHom.id ℂ) := IsAlgClosed.splits_codomain p
  have hcard_nd : p.roots.card = p.natDegree := splits_iff_card_roots.mp hp_splits
  have hcard6 : p.roots.card = 6 := by rw [hcard_nd, hp_deg]
  have hroot_props : ∀ z ∈ p.roots, z.im = 0 ∧ 0 < z.re ∧ ↑(Int.floor z.re) = z.re := by
    intro z hz; exact h₁ z (by rw [← heval]; rwa [mem_roots hp_ne] at hz)
  have hp_prod_eq : (p.roots.map (fun r => X - C r)).prod = p :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp_monic hcard_nd
  -- Vieta: product of roots = 16
  have hprod : p.roots.prod = 16 := by
    have h0 := coeff_zero_eq_prod_roots_of_monic_of_splits hp_monic hp_splits
    rw [hp_deg] at h0
    have hc0 : p.coeff 0 = 16 := by
      rw [show_p]
      simp only [coeff_add, coeff_sub, coeff_mul, coeff_X, coeff_C, coeff_X_pow,
        Finset.antidiagonal]
      simp (config := { decide := true })
    rw [hc0] at h0
    have : ((-1 : ℂ) ^ 6) = 1 := by norm_num
    rw [this, one_mul] at h0; exact h0.symm
  -- Vieta: sum of roots = 10
  have hsum : p.roots.sum = 10 := by
    have h0 := nextCoeff_eq_neg_sum_roots_of_monic_of_splits hp_monic hp_splits
    have hnc : p.nextCoeff = -10 := by
      unfold nextCoeff; rw [hp_deg]
      simp only [show (6 : ℕ) ≠ 0 from by norm_num, ↓reduceIte, show 6 - 1 = 5 from rfl]
      rw [show_p]
      simp only [coeff_add, coeff_sub, coeff_mul, coeff_X, coeff_C, coeff_X_pow,
        Finset.antidiagonal]
      simp (config := { decide := true })
    rw [hnc] at h0
    -- h0 : (-10 : ℂ) = -p.roots.sum
    exact (neg_injective h0).symm
  -- Each root r satisfies: r.im = 0, r.re is a positive integer
  have hroot_int : ∀ r ∈ p.roots, r = (↑(⌊r.re⌋ : ℤ) : ℂ) := by
    intro r hr; obtain ⟨him, _, hfl⟩ := hroot_props r hr
    -- hfl : (↑⌊r.re⌋ : ℝ) = r.re
    have hre : r.re = (↑(⌊r.re⌋ : ℤ) : ℂ).re := by
      simp only [Complex.intCast_re]; linarith [hfl]
    have him' : r.im = (↑(⌊r.re⌋ : ℤ) : ℂ).im := by
      simp only [Complex.intCast_im]; exact him
    exact Complex.ext hre him'
  have hroot_ge1 : ∀ r ∈ p.roots, (1 : ℤ) ≤ ⌊r.re⌋ := by
    intro r hr; obtain ⟨_, hre, hfl⟩ := hroot_props r hr
    -- hfl : (↑⌊r.re⌋ : ℝ) = r.re, hre : 0 < r.re
    have hfl_re : (⌊r.re⌋ : ℝ) = r.re := by exact_mod_cast hfl
    have : (0 : ℝ) < (⌊r.re⌋ : ℝ) := by linarith
    exact_mod_cast this
  -- Transfer to integer multiset S
  set S : Multiset ℤ := p.roots.map (fun z => ⌊z.re⌋) with hS_def
  have hS_map_eq : S.map (Int.cast : ℤ → ℂ) = p.roots := by
    rw [hS_def, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id p.roots]
    exact Multiset.map_congr rfl fun r hr => (hroot_int r hr).symm
  have hS_card : S.card = 6 := by simp [hS_def, hcard6]
  have hS_ge1 : ∀ n ∈ S, (1 : ℤ) ≤ n := by
    intro n hn; obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hn; exact hroot_ge1 r hr
  have hS_prod : S.prod = 16 := by
    have h1 : (S.map (Int.cast : ℤ → ℂ)).prod = 16 := by rw [hS_map_eq, hprod]
    have h2 : (S.map (Int.cast : ℤ → ℂ)).prod = ((S.prod : ℤ) : ℂ) := by
      induction S using Multiset.induction with
      | empty => simp
      | cons a t ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons]
        rw [ih]; push_cast; ring
    rw [h2] at h1; exact_mod_cast h1
  have hS_sum : S.sum = 10 := by
    have h1 : (S.map (Int.cast : ℤ → ℂ)).sum = 10 := by rw [hS_map_eq, hsum]
    have h2 : (S.map (Int.cast : ℤ → ℂ)).sum = ((S.sum : ℤ) : ℂ) := by
      induction S using Multiset.induction with
      | empty => simp
      | cons a t ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        rw [ih]; push_cast; ring
    rw [h2] at h1; exact_mod_cast h1
  have hS_dvd : ∀ n ∈ S, n ∣ 16 := fun n hn => hS_prod ▸ Multiset.dvd_prod hn
  -- Each element ≤ 5 (sum = 10, 6 elements each ≥ 1, so max ≤ 10 - 5 = 5)
  have hS_le5 : ∀ n ∈ S, n ≤ 5 := by
    intro n hn
    have herase_sum : n + (S.erase n).sum = 10 := by
      have := Multiset.sum_erase hn; linarith [hS_sum]
    have herase_card : (S.erase n).card = 5 := by
      have h := Multiset.card_erase_of_mem hn
      rw [hS_card] at h; exact h
    have herase_ge : ∀ m ∈ S.erase n, (1 : ℤ) ≤ m :=
      fun m hm => hS_ge1 m (Multiset.erase_subset n S hm)
    have h5 : (5 : ℤ) ≤ (S.erase n).sum := by
      have h := Multiset.card_nsmul_le_sum herase_ge
      rw [herase_card] at h; simpa using h
    linarith
  -- Each element is 1 or 2
  have hS_12 : ∀ n ∈ S, n = 1 ∨ n = 2 := by
    intro n hn
    have hge := hS_ge1 n hn
    have hdvd := hS_dvd n hn
    have hle := hS_le5 n hn
    have hne3 : n ≠ 3 := by intro h; subst h; norm_num at hdvd
    have hne5 : n ≠ 5 := by intro h; subst h; norm_num at hdvd
    -- Rule out n = 4
    have hne4 : n ≠ 4 := by
      intro h; subst h
      have hprod_erase : (S.erase 4).prod = 4 := by
        have := Multiset.prod_erase hn; linarith [hS_prod]
      have hsum_erase : (S.erase 4).sum = 6 := by
        have := Multiset.sum_erase hn; linarith [hS_sum]
      have hcard_erase : (S.erase 4).card = 5 := by
        have h := Multiset.card_erase_of_mem hn; rw [hS_card] at h; exact h
      have hge_erase : ∀ m ∈ S.erase 4, (1 : ℤ) ≤ m :=
        fun m hm => hS_ge1 m (Multiset.erase_subset 4 S hm)
      have hle_erase : ∀ m ∈ S.erase 4, m ≤ 2 := by
        intro m hm
        have hm_sum : m + ((S.erase 4).erase m).sum = 6 := by
          have := Multiset.sum_erase hm; linarith [hsum_erase]
        have hm_card : ((S.erase 4).erase m).card = 4 := by
          have h := Multiset.card_erase_of_mem hm; rw [hcard_erase] at h; exact h
        have hm_ge : ∀ k ∈ (S.erase 4).erase m, (1 : ℤ) ≤ k :=
          fun k hk => hge_erase k (Multiset.erase_subset m _ hk)
        have : (4 : ℤ) ≤ ((S.erase 4).erase m).sum := by
          have := Multiset.card_nsmul_le_sum hm_ge
          rw [hm_card] at this; simpa using this
        linarith
      have h12_erase : ∀ m ∈ S.erase 4, m = 1 ∨ m = 2 := by
        intro m hm; have := hge_erase m hm; have := hle_erase m hm; omega
      set T := S.erase 4 with hT_def
      have hT_decomp : T = Multiset.replicate (T.count 1) 1 + Multiset.replicate (T.count 2) 2 := by
        ext x
        simp only [Multiset.count_add, Multiset.count_replicate]
        by_cases hx1 : x = 1
        · subst hx1; simp
        · by_cases hx2 : x = 2
          · subst hx2; simp
          · have : Multiset.count x T = 0 :=
              Multiset.count_eq_zero.mpr fun hm => (h12_erase x hm).elim hx1 hx2
            -- Goal has if (1 = x) and if (2 = x)
            rw [this]; simp [Ne.symm hx1, Ne.symm hx2]
      have hT_card : T.count 1 + T.count 2 = 5 := by
        have := hcard_erase
        rw [hT_decomp, Multiset.card_add, Multiset.card_replicate, Multiset.card_replicate] at this
        exact this
      have hT_sum_eq : (T.count 1 : ℤ) + 2 * T.count 2 = 6 := by
        have := hsum_erase
        rw [hT_decomp, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate] at this
        rw [nsmul_eq_mul, mul_one, nsmul_eq_mul, mul_comm] at this
        exact this
      have hT_c2 : T.count 2 = 1 := by omega
      have hT_c1 : T.count 1 = 4 := by omega
      have hT_prod : T.prod = 2 := by
        rw [hT_decomp, Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate,
          hT_c1, hT_c2]; norm_num
      linarith
    omega
  -- Each root is 1 or 2 in ℂ
  have hroot_12 : ∀ r ∈ p.roots, r = 1 ∨ r = 2 := by
    intro r hr
    have hmem : ⌊r.re⌋ ∈ S := Multiset.mem_map.mpr ⟨r, hr, rfl⟩
    rcases hS_12 _ hmem with h | h
    · left; rw [hroot_int r hr, h]; push_cast; rfl
    · right; rw [hroot_int r hr, h]; push_cast; rfl
  -- Decompose p.roots
  have hroots_decomp : p.roots = Multiset.replicate (p.roots.count 1) (1 : ℂ) +
      Multiset.replicate (p.roots.count 2) (2 : ℂ) := by
    ext x
    simp only [Multiset.count_add, Multiset.count_replicate]
    by_cases hx1 : x = 1
    · subst hx1; simp
    · by_cases hx2 : x = 2
      · subst hx2; simp
      · have hcount0 : Multiset.count x p.roots = 0 :=
          Multiset.count_eq_zero.mpr fun hm => (hroot_12 x hm).elim hx1 hx2
        rw [hcount0]; simp [Ne.symm hx1, Ne.symm hx2]
  have hcount_card : p.roots.count 1 + p.roots.count 2 = 6 := by
    have := hcard6; rw [hroots_decomp, Multiset.card_add, Multiset.card_replicate,
      Multiset.card_replicate] at this; exact this
  have hcount_sum : p.roots.count 1 + 2 * p.roots.count 2 = 10 := by
    have hsR : p.roots.sum = 10 := hsum
    rw [hroots_decomp, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate] at hsR
    rw [nsmul_eq_mul, mul_one, nsmul_eq_mul, mul_comm] at hsR
    exact_mod_cast hsR
  have hc1 : p.roots.count 1 = 2 := by omega
  have hc2 : p.roots.count 2 = 4 := by omega
  -- p.roots = {1, 1, 2, 2, 2, 2}
  suffices hroots_eq : p.roots = {1, 1, 2, 2, 2, 2} by
    intro z; rw [← heval]
    have hp_eq : p = (X - C 1) ^ 2 * (X - C 2) ^ 4 := by
      rw [← hp_prod_eq, hroots_eq]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_singleton, Multiset.prod_singleton]
      ring
    rw [hp_eq]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  rw [hroots_decomp, hc1, hc2]
  rfl
