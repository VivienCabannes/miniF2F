import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 3200000

/-- If p prime, p ≥ 3, p | 2^n+1, n odd, n > 0, all prime factors of n ≥ p, then p = 3. -/
private lemma ord_argument {p n : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hdvd : p ∣ 2 ^ n + 1) (hodd : ¬ 2 ∣ n) (hn : 0 < n)
    (hmin : ∀ q, Nat.Prime q → q ∣ n → p ≤ q) : p = 3 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (2 < p) := ⟨by omega⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h; have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hpn : (2 : ZMod p) ^ n = -1 := by
    have h0 : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have h1 : (2 : ZMod p) ^ n + 1 = 0 := by push_cast at h0 ⊢; exact h0
    exact eq_neg_of_add_eq_zero_left h1
  have h2n : (2 : ZMod p) ^ (2 * n) = 1 := by
    rw [show 2 * n = n + n from by ring, pow_add, hpn]; ring
  set d := orderOf (2 : ZMod p) with hd_def
  have hd_pos : 0 < d := by
    rw [hd_def, orderOf_pos_iff]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * n, by omega, h2n⟩
  have hd_dvd_2n : d ∣ 2 * n := orderOf_dvd_of_pow_eq_one h2n
  have hd_ndvd_n : ¬ d ∣ n := fun h =>
    (show (2 : ZMod p) ^ n ≠ 1 by rw [hpn]; exact ZMod.neg_one_ne_one)
      (orderOf_dvd_iff_pow_eq_one.mp h)
  have hd_dvd_pm1 : d ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2ne
  have hd_even : 2 ∣ d := by
    by_contra hd_odd
    exact hd_ndvd_n ((Nat.coprime_comm.mpr
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr hd_odd)).dvd_of_dvd_mul_left hd_dvd_2n)
  obtain ⟨e, he⟩ := hd_even
  have he_dvd_n : e ∣ n := (mul_dvd_mul_iff_left (show (2 : ℕ) ≠ 0 from by omega)).mp (he ▸ hd_dvd_2n)
  have he1 : e = 1 := by
    by_contra he_ne
    have hq := Nat.minFac_prime he_ne
    have hqe := Nat.minFac_dvd e
    have : p ≤ e.minFac := hmin _ hq (dvd_trans hqe he_dvd_n)
    have : e.minFac ≤ p - 1 := Nat.le_of_dvd (by omega)
      (dvd_trans (dvd_trans hqe (Dvd.intro_left 2 he.symm)) hd_dvd_pm1)
    omega
  subst he1; simp at he
  have h2sq : (2 : ZMod p) ^ 2 = 1 := by rw [← he, hd_def]; exact pow_orderOf_eq_one _
  have key : ((4 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    change ((2 ^ 2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p)
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]; exact h2sq
  rw [ZMod.natCast_eq_natCast_iff] at key
  have hp3' : p ∣ 3 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ 4)).mp key.symm
  rcases (show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd p hp3' with h | h <;> omega

/-- If q ≥ 5 prime, q | 2^(3m)+1, m odd, 3 ∤ m, q = m.minFac, then q = 7. -/
private lemma q_eq_seven {q m : ℕ} (hq : Nat.Prime q) (hq5 : 5 ≤ q)
    (hdvd : q ∣ 2 ^ (3 * m) + 1) (hodd_m : ¬ 2 ∣ m) (hm : 0 < m) (h3m : ¬ 3 ∣ m)
    (hmin : ∀ r, Nat.Prime r → r ∣ m → q ≤ r) : q = 7 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : Fact (2 < q) := ⟨by omega⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h; have : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  set n := 3 * m
  have hodd_n : ¬ 2 ∣ n := fun h => hodd_m (by rcases h with ⟨k, hk⟩; exact ⟨_, by omega⟩)
  have hpn : (2 : ZMod q) ^ n = -1 := by
    have h0 : ((2 ^ n + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have h1 : (2 : ZMod q) ^ n + 1 = 0 := by push_cast at h0 ⊢; exact h0
    exact eq_neg_of_add_eq_zero_left h1
  have h2n : (2 : ZMod q) ^ (2 * n) = 1 := by
    rw [show 2 * n = n + n from by ring, pow_add, hpn]; ring
  set d := orderOf (2 : ZMod q)
  have hd_pos : 0 < d := by
    rw [orderOf_pos_iff]; exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * n, by omega, h2n⟩
  have hd_dvd : d ∣ 2 * n := orderOf_dvd_of_pow_eq_one h2n
  have hd_ndvd : ¬ d ∣ n := fun h =>
    (show (2 : ZMod q) ^ n ≠ 1 by rw [hpn]; exact ZMod.neg_one_ne_one)
      (orderOf_dvd_iff_pow_eq_one.mp h)
  have hd_qm1 : d ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one h2ne
  have hd_even : 2 ∣ d := by
    by_contra hd_odd
    exact hd_ndvd ((Nat.coprime_comm.mpr
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr hd_odd)).dvd_of_dvd_mul_left hd_dvd)
  obtain ⟨e, he⟩ := hd_even
  have he_dvd : e ∣ 3 * m :=
    (mul_dvd_mul_iff_left (show (2 : ℕ) ≠ 0 from by omega)).mp (he ▸ hd_dvd)
  -- Every prime factor r of e: r | d | q-1, so r < q. Also r | 3m.
  -- Since r < q ≤ m.minFac, r ∤ m. So r | 3, r = 3.
  -- Hence e | 3 (since all prime factors are 3 and e | 3m with 3 ∤ m).
  have he3 : e ∣ 3 := by
    by_contra he_not_3
    have he_ne_1 : e ≠ 1 := fun h => by simp [h] at he_not_3
    -- e has a prime factor
    set r := e.minFac
    have hr_prime := Nat.minFac_prime he_ne_1
    have hr_dvd_e := Nat.minFac_dvd e
    -- r | d | q-1, so r < q
    have hr_lt_q : r < q := by
      have : r ≤ q - 1 := Nat.le_of_dvd (by omega)
        (dvd_trans (dvd_trans hr_dvd_e (Dvd.intro_left 2 he.symm)) hd_qm1)
      omega
    -- r | e | 3m
    have hr_3m : r ∣ 3 * m := dvd_trans hr_dvd_e he_dvd
    -- r | 3 or r | m
    rcases hr_prime.dvd_mul.mp hr_3m with hr3 | hrm
    · -- r | 3, r prime, so r = 3
      have hr3' : r = 3 := ((show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd r hr3).resolve_left
        (by omega)
      -- 3 | e. Show: 3 | e and e | 3m and 3 ∤ m means e = 3.
      -- But we said e ∤ 3 (he_not_3). If 3 | e and e ≤ 3m:
      -- e/3 | m (since e | 3m and 3 | e). If e/3 > 1, e/3 has a prime factor s.
      -- s | e/3 | m, so s ≥ q. But s | e/3 | e, so s | d | q-1, so s < q. Contradiction.
      -- So e/3 = 1, e = 3. But e ∤ 3, contradiction (since 3 | 3).
      rw [hr3'] at hr_dvd_e
      have h3e := hr_dvd_e
      have he3_dvd : e / 3 ∣ m := by
        have := Nat.div_dvd_of_dvd h3e
        have : 3 * (e / 3) ∣ 3 * m := by rwa [Nat.mul_div_cancel' h3e]
        exact (mul_dvd_mul_iff_left (show (3 : ℕ) ≠ 0 from by omega)).mp this
      by_cases he3_eq : e / 3 = 1
      · have : e = 3 := by omega
        exact he_not_3 ⟨1, by omega⟩
      · have hs := Nat.minFac_prime he3_eq
        have hs_dvd := Nat.minFac_dvd (e / 3)
        have : q ≤ (e / 3).minFac := hmin _ hs (dvd_trans hs_dvd he3_dvd)
        have : (e / 3).minFac ≤ q - 1 := by
          have : (e / 3).minFac ∣ q - 1 :=
            dvd_trans (dvd_trans hs_dvd (Nat.div_dvd_of_dvd h3e)) (dvd_trans (Dvd.intro_left 2 he.symm) hd_qm1)
          exact Nat.le_of_dvd (by omega) this
        omega
    · -- r | m, so r ≥ q. But r < q. Contradiction.
      exact absurd (hmin r hr_prime hrm) (by omega)
  have hd_cases : d = 2 ∨ d = 6 := by
    rcases he3 with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      rcases k with _ | k
      · simp at hk; omega
      · omega
    have hk_le3 : k ≤ 3 := by
      have : e ≤ 3 := Nat.le_of_dvd (by omega) he3
      omega
    interval_cases k <;> omega
  rcases hd_cases with hd2 | hd6
  · -- d = 2: q | 3, but q ≥ 5
    have h2sq : (2 : ZMod q) ^ 2 = 1 := by rw [← hd2]; exact pow_orderOf_eq_one _
    have key : ((4 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      change ((2 ^ 2 : ℕ) : ZMod q) = _; simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]; exact h2sq
    rw [ZMod.natCast_eq_natCast_iff] at key
    have : q ∣ 3 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ 4)).mp key.symm
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  · -- d = 6: q | 63 = 7*9, q ≥ 5, q prime → q = 7
    have h6 : (2 : ZMod q) ^ 6 = 1 := by rw [← hd6]; exact pow_orderOf_eq_one _
    have key : ((64 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      change ((2 ^ 6 : ℕ) : ZMod q) = _; simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]; exact h6
    rw [ZMod.natCast_eq_natCast_iff] at key
    have hq63 : q ∣ 63 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ 64)).mp key.symm
    have : q ∣ 7 * 9 := by rwa [show (63 : ℕ) = 7 * 9 from by norm_num] at hq63
    rcases hq.dvd_mul.mp this with h | h
    · exact ((show Nat.Prime 7 from by norm_num).eq_one_or_self_of_dvd q h).resolve_left (by omega)
    · have : q ∣ 3 ^ 2 := by rwa [show (9 : ℕ) = 3 ^ 2 from by norm_num] at h
      rcases (show Nat.Prime 3 from by norm_num).eq_one_or_self_of_dvd q (hq.dvd_of_dvd_pow this) with h | h <;> omega

theorem imo_1990_p3 (n : ℕ) (h₀ : 2 ≤ n) (h₁ : n ^ 2 ∣ 2 ^ n + 1) : n = 3 := by
  -- Step 1: n is odd
  have hodd : ¬ 2 ∣ n := by
    intro ⟨k, hk⟩
    have hne : n ≠ 0 := by omega
    have : 2 ∣ n ^ 2 := ⟨k * n, by ring_nf; omega⟩
    have : 2 ∣ 2 ^ n + 1 := dvd_trans this h₁
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 hne
    omega
  have hn3 : 3 ≤ n := by omega
  -- Step 2: n.minFac = 3
  have hmf_prime := Nat.minFac_prime (show n ≠ 1 by omega)
  have hmf_dvd := Nat.minFac_dvd n
  have hmf3 : 3 ≤ n.minFac := by
    have : n.minFac ≠ 2 := fun h => hodd ((Nat.minFac_eq_two_iff n).mp h)
    exact Nat.lt_of_le_of_ne hmf_prime.two_le (Ne.symm this)
  have hmf_dvd' : n.minFac ∣ 2 ^ n + 1 :=
    dvd_trans (dvd_trans (dvd_pow_self n.minFac (by omega))
      (pow_dvd_pow_of_dvd hmf_dvd 2)) h₁
  have hmf_eq : n.minFac = 3 := ord_argument hmf_prime hmf3 hmf_dvd' hodd (by omega)
    (fun q hq hqn => Nat.minFac_le_of_dvd hq.two_le hqn)
  -- Step 3: 3 | n, write n = 3m
  have h3n : 3 ∣ n := hmf_eq ▸ hmf_dvd
  obtain ⟨m, rfl⟩ := h3n
  have hm_pos : 0 < m := by omega
  have hm_odd : ¬ 2 ∣ m := fun ⟨k, hk⟩ => hodd ⟨3 * k, by omega⟩
  -- Step 4: 3 ∤ m (using Lifting the Exponent Lemma)
  have h3nm : ¬ 3 ∣ m := by
    intro h3m
    have h3p : Nat.Prime 3 := by norm_num
    have h3prime : _root_.Prime (3 : ℕ) := h3p.prime
    have h3odd : Odd (3 : ℕ) := ⟨1, by omega⟩
    have hm_odd' : Odd m := Nat.not_even_iff_odd.mp (fun h => hm_odd h.two_dvd)
    have hn_odd : Odd (3 * m) := h3odd.mul hm_odd'
    have hlte := Nat.emultiplicity_pow_add_pow h3p h3odd
      (show (3 : ℕ) ∣ 2 + 1 from by norm_num) (show ¬ (3 : ℕ) ∣ 2 from by omega) hn_odd
    simp only [one_pow] at hlte
    have hem3 : emultiplicity (3 : ℕ) 3 = 1 := Nat.Prime.emultiplicity_self h3p
    have hem3m : emultiplicity (3 : ℕ) (3 * m) = 1 + emultiplicity (3 : ℕ) m := by
      rw [emultiplicity_mul h3prime, hem3]
    rw [hem3, hem3m] at hlte
    have hle := emultiplicity_le_emultiplicity_of_dvd_right h₁ (a := (3 : ℕ))
    rw [emultiplicity_pow h3prime, hem3m, hlte] at hle
    have hem1 : 1 ≤ emultiplicity (3 : ℕ) m := le_emultiplicity_of_pow_dvd (by simpa using h3m)
    have hfin : emultiplicity (3 : ℕ) m ≠ ⊤ :=
      finiteMultiplicity_iff_emultiplicity_ne_top.mp (Nat.finiteMultiplicity_iff.mpr ⟨by omega, hm_pos⟩)
    obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hfin
    norm_cast at hle hem1; omega
  -- Step 5: m = 1 (if m > 1, get contradiction via q = 7 and 49 ∤ 2^(21t)+1)
  suffices m = 1 by omega
  by_contra hm_ne_1
  have hm_gt1 : m > 1 := by omega
  set q := m.minFac
  have hq_prime := Nat.minFac_prime (show m ≠ 1 by omega)
  have hq_dvd := Nat.minFac_dvd m
  have hq5 : 5 ≤ q := by
    have hq2 : q ≠ 2 := fun h => hm_odd (h ▸ hq_dvd)
    have hq3 : q ≠ 3 := fun h => h3nm (h ▸ hq_dvd)
    have := hq_prime.two_le
    have hq4 : q ≠ 4 := fun h => by
      have : ¬ Nat.Prime 4 := by norm_num
      exact this (h ▸ hq_prime)
    omega
  have hq_dvd_n : q ∣ 3 * m := dvd_trans hq_dvd (dvd_mul_left m 3)
  have hq_dvd' : q ∣ 2 ^ (3 * m) + 1 :=
    dvd_trans (dvd_trans (dvd_pow_self q (by omega)) (pow_dvd_pow_of_dvd hq_dvd_n 2)) h₁
  have hq7 : q = 7 := q_eq_seven hq_prime hq5 hq_dvd' hm_odd hm_pos h3nm
    (fun r hr hrm => Nat.minFac_le_of_dvd hr.two_le hrm)
  have h7_dvd : (7 : ℕ) ∣ m := hq7 ▸ hq_dvd
  obtain ⟨t, rfl⟩ := h7_dvd
  have ht_pos : 0 < t := by omega
  have h49 : 49 ∣ 2 ^ (3 * (7 * t)) + 1 := by
    have : 49 ∣ (3 * (7 * t)) ^ 2 := by
      rw [show 49 = 7 ^ 2 from by norm_num]
      exact pow_dvd_pow_of_dvd (show 7 ∣ 3 * (7 * t) from ⟨3 * t, by ring⟩) 2
    exact dvd_trans this h₁
  have hn_eq : 3 * (7 * t) = 21 * t := by ring
  rw [hn_eq] at h49
  have h_mod : 2 ^ (21 * t) % 49 = 1 := by rw [pow_mul, Nat.pow_mod]; norm_num
  have h_mod2 : (2 ^ (21 * t) + 1) % 49 = 2 := by omega
  exact absurd h49 (by rw [Nat.dvd_iff_mod_eq_zero]; omega)
