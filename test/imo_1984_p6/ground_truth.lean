import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 3200000

theorem imo_1984_p6
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2^k)
  (h₅ : b + c = 2^m) :
  a = 1 := by
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  obtain ⟨ha_odd, hb_odd, hc_odd, hd_odd⟩ := h₁
  obtain ⟨hab, hbc, hcd⟩ := h₂
  have ha_odd' := ha_odd
  have hc_odd' := hc_odd
  obtain ⟨u, hu⟩ := ha_odd
  obtain ⟨v, hv⟩ := hb_odd
  obtain ⟨w, hw⟩ := hc_odd
  have huv : u < v := by omega
  -- Step 1: b + c ≤ a + d, hence m ≤ k
  have hsum : b + c ≤ a + d := by
    suffices a * (b + c) ≤ a * (a + d) from Nat.le_of_mul_le_mul_left this ha
    nlinarith [h₃]
  have hkm : m ≤ k := by
    by_contra hmk
    push_neg at hmk
    have h1 : 2 ^ k < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hmk
    omega
  -- Step 2: m ≥ 3
  have hm3 : 3 ≤ m := by
    have h1 : 8 ≤ b + c := by omega
    rw [h₅] at h1
    by_contra hm; push_neg at hm; interval_cases m <;> omega
  -- Power identities
  have hpow_m1 : 2 * 2^(m-2) = 2^(m-1) := by
    have : 2^(m-1) = 2^(m-2) * 2 := by rw [← pow_succ]; congr 1; omega
    linarith
  have hpow_m : 2 * 2^(m-1) = 2^m := by
    have : 2^m = 2^(m-1) * 2 := by rw [← pow_succ]; congr 1; omega
    linarith
  -- Step 3: b < 2^(m-1) and a+b < 2^m
  have hb_lt : b < 2^(m-1) := by nlinarith [hpow_m]
  have hab_lt : a + b < 2^m := by omega
  -- Step 4: Define s = v - u and t = u + v + 1
  set s := v - u
  set t := u + v + 1
  have hs_pos : 0 < s := by omega
  have ht_pos : 0 < t := by omega
  have hab_eq : a + b = 2 * t := by omega
  -- Step 5: Key equation and 2^(m-2) | s*t
  have heq_z : ((b : ℤ) - a) * (b + a) = 2^m * (b - 2^(k-m) * a) := by
    have h3 := h₃; have h4 := h₄; have h5 := h₅
    zify at h3 h4 h5 ⊢
    have : (2 : ℤ)^k = 2^m * 2^(k-m) := by rw [← pow_add]; congr 1; omega
    nlinarith
  have hdiv_st : 2^(m-2) ∣ s * t := by
    have h4st_z : ((b : ℤ) - a) * (b + a) = 4 * ↑s * ↑t := by
      have hba : (b : ℤ) - a = 2 * ↑s := by omega
      have hab : (b : ℤ) + a = 2 * ↑t := by omega
      rw [hba, hab]; ring
    have hdiv_z : (2 : ℤ)^m ∣ 4 * ↑s * ↑t := by rw [← h4st_z]; exact ⟨↑b - 2^(k-m) * ↑a, heq_z⟩
    have hdiv_4st : 2^m ∣ 4 * s * t := by
      have : ((2^m : ℕ) : ℤ) ∣ ((4 * s * t : ℕ) : ℤ) := by push_cast; exact hdiv_z
      exact_mod_cast this
    have h1 : 4 * s * t = 2^2 * (s * t) := by ring
    rw [h1] at hdiv_4st
    have h2 : 2^m = 2^2 * 2^(m-2) := by rw [← pow_add]; congr 1; omega
    rw [h2] at hdiv_4st
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2^2)).mp hdiv_4st
  -- Step 6: s is odd
  have hs_lt : s < 2^(m-2) := by
    have : 2 * s < b := by omega
    nlinarith [hpow_m1, hb_lt]
  have hs_odd : Odd s := by
    by_contra hs_even; rw [Nat.not_odd_iff_even] at hs_even
    have ht_odd : Odd t := by rw [show t = s + a from by omega]; exact hs_even.add_odd ha_odd'
    have hcop : Nat.Coprime (2^(m-2)) t :=
      ((Nat.coprime_two_right.mpr ht_odd).pow_right (m-2)).symm
    exact absurd (Nat.le_of_dvd hs_pos (hcop.dvd_of_dvd_mul_right hdiv_st)) (not_le.mpr hs_lt)
  -- Step 7: 2^(m-2) | t → t = 2^(m-2)
  have hdvd_t : 2^(m-2) ∣ t := by
    rw [mul_comm] at hdiv_st
    exact (((Nat.coprime_two_right.mpr hs_odd).pow_right (m-2)).symm).dvd_of_dvd_mul_right hdiv_st
  have ht_eq : t = 2^(m-2) := by
    obtain ⟨q, hq⟩ := hdvd_t
    have hq_pos : 0 < q := by
      by_contra hq0; push_neg at hq0
      have : q = 0 := by omega
      subst this; simp at hq; omega
    have hq1 : q < 2 := by nlinarith [hpow_m1]
    have hq_eq : q = 1 := by omega
    rw [hq_eq, mul_one] at hq; exact hq
  -- Step 8: a + b = 2^(m-1), derive 2^(k-m)*a = 2^(m-2)
  have hab_pow : a + b = 2^(m-1) := by rw [hab_eq, ht_eq, hpow_m1]
  have hkey_z : 2^(k-m) * (a : ℤ) = 2^(m-2) := by
    have hba_z : ((b : ℤ) - a) = 2 * ↑s := by
      have hab' : a ≤ b := by omega
      have : b - a = 2 * s := by omega
      zify [hab'] at this; linarith
    have hab_z : ((b : ℤ) + a) = 2 * ↑t := by
      have : a + b = 2 * t := hab_eq
      zify at this; linarith
    have ht_z : (t : ℤ) = 2^(m-2) := by exact_mod_cast ht_eq
    have hs_eq : (s : ℤ) = b - 2^(k-m) * a := by
      have h0 : ((b : ℤ) - a) * (b + a) = 2 * ↑s * (2 * 2^(m-2 : ℕ)) := by
        rw [hba_z, hab_z, ht_z]
      have h1 : (2 : ℤ)^m * s = 2^m * ((b : ℤ) - 2^(k-m) * a) := by
        have h2 : (2 : ℤ) * 2^(m-2 : ℕ) = 2^(m-1 : ℕ) := by exact_mod_cast hpow_m1
        have h3 : (2 : ℤ) * 2^(m-1 : ℕ) = 2^m := by exact_mod_cast hpow_m
        nlinarith [heq_z, h0, h2, h3]
      exact mul_left_cancel₀ (show (2 : ℤ)^m ≠ 0 by positivity) h1
    have hb_eq : (b : ℤ) = s + 2^(m-2 : ℕ) := by
      have : b = s + t := by omega
      push_cast [this]; exact congrArg _ ht_z
    linarith
  -- Step 9: a | 2^(m-2), Coprime a (2^(m-2)) → a = 1
  have hkey : 2^(k-m) * a = 2^(m-2) := by exact_mod_cast hkey_z
  have ha_dvd : a ∣ 2^(m-2) := ⟨2^(k-m), by linarith⟩
  exact Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_two_right.mpr ha_odd').pow_right (m-2)) dvd_rfl ha_dvd
