import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 6400000

/-! # AMC 12A 2021 Problem 25

The function f(n) = d(n)/n^(1/3) is uniquely maximized at N = 2520 = 2³·3²·5·7,
and the digit sum of 2520 is 9.

## Proof outline
1. Per-prime bounds: for each prime p, (e+1)^3 ≤ C(p) * p^e.
2. Strip factors of 2, 3, 5, 7 from n to get t with all prime factors ≥ 11.
3. Use d(t)^3 ≤ t and multiply per-prime bounds to get 35·d(n)^3 ≤ 1536·n.
4. Conclude d(n)^3·2520 ≤ 110592·n (since 2520 = 35·72 and 1536·72 = 110592).
5. This means f(2520) ≥ f(n) for all n, so N = 2520. Digit sum = 9.
-/

-- Per-prime bounds
private lemma bound_prime2 (e : ℕ) : (e + 1) ^ 3 ≤ 8 * 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    match e with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num
    | n + 3 =>
      have h1 : (n + 5) ^ 3 ≤ 2 * (n + 4) ^ 3 := by
        have : n ^ 3 + 9 * n ^ 2 + 24 * n + 3 ≥ 0 := Nat.zero_le _; nlinarith
      linarith [show 2 * (8 * 2 ^ (n + 3)) = 8 * 2 ^ (n + 3 + 1) from by ring]

private lemma bound_prime3 (e : ℕ) : (e + 1) ^ 3 ≤ 3 ^ (e + 1) := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    match e with
    | 0 => norm_num
    | 1 => norm_num
    | n + 2 =>
      have h1 : (n + 4) ^ 3 ≤ 3 * (n + 3) ^ 3 := by
        have : 2 * n ^ 3 + 15 * n ^ 2 + 33 * n + 17 ≥ 0 := Nat.zero_le _; nlinarith
      linarith [show 3 * 3 ^ (n + 3) = 3 ^ (n + 2 + 1 + 1) from by ring]

private lemma bound_prime5 (e : ℕ) : 5 * (e + 1) ^ 3 ≤ 8 * 5 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    match e with
    | 0 => norm_num
    | n + 1 =>
      have h1 : (n + 3) ^ 3 ≤ 5 * (n + 2) ^ 3 := by
        have : 4 * n ^ 3 + 21 * n ^ 2 + 33 * n + 13 ≥ 0 := Nat.zero_le _; nlinarith
      calc 5 * (n + 1 + 1 + 1) ^ 3 = 5 * (n + 3) ^ 3 := by ring_nf
        _ ≤ 5 * (5 * (n + 2) ^ 3) := by linarith
        _ = 25 * (n + 2) ^ 3 := by ring
        _ ≤ 5 * (8 * 5 ^ (n + 1)) := by linarith
        _ = 8 * 5 ^ (n + 1 + 1) := by ring

private lemma bound_prime7 (e : ℕ) : 7 * (e + 1) ^ 3 ≤ 8 * 7 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    match e with
    | 0 => norm_num
    | n + 1 =>
      have h1 : (n + 3) ^ 3 ≤ 7 * (n + 2) ^ 3 := by
        have : 6 * n ^ 3 + 33 * n ^ 2 + 57 * n + 29 ≥ 0 := Nat.zero_le _; nlinarith
      calc 7 * (n + 1 + 1 + 1) ^ 3 = 7 * (n + 3) ^ 3 := by ring_nf
        _ ≤ 7 * (7 * (n + 2) ^ 3) := by linarith
        _ = 49 * (n + 2) ^ 3 := by ring
        _ ≤ 7 * (8 * 7 ^ (n + 1)) := by linarith
        _ = 8 * 7 ^ (n + 1 + 1) := by ring

private lemma bound_prime_ge11 (p : ℕ) (hp : 11 ≤ p) (e : ℕ) : (e + 1) ^ 3 ≤ p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    match e with
    | 0 =>
      calc (0 + 1 + 1) ^ 3 = 8 := by norm_num
        _ ≤ 11 := by norm_num
        _ ≤ p := hp
        _ = p ^ 1 := (pow_one p).symm
    | 1 =>
      calc (1 + 1 + 1) ^ 3 = 27 := by norm_num
        _ ≤ 121 := by norm_num
        _ = 11 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
    | n + 2 =>
      have h1 : (n + 4) ^ 3 ≤ 11 * (n + 3) ^ 3 := by
        have : 10 * n ^ 3 + 87 * n ^ 2 + 249 * n + 233 ≥ 0 := Nat.zero_le _; nlinarith
      calc (n + 2 + 1 + 1) ^ 3 = (n + 4) ^ 3 := by ring_nf
        _ ≤ 11 * (n + 3) ^ 3 := h1
        _ ≤ p * (n + 3) ^ 3 := Nat.mul_le_mul_right _ hp
        _ ≤ p * p ^ (n + 2) := Nat.mul_le_mul_left _ ih
        _ = p ^ (n + 2 + 1) := by ring

-- Helper: d(p^e * m) = (e+1) * d(m) when p prime and p ∤ m
private lemma card_div_prime_pow_mul (p m e : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) :
    (Nat.divisors (p ^ e * m)).card = (e + 1) * (Nat.divisors m).card := by
  have hcop := (hp.coprime_iff_not_dvd.mpr hm).pow_left e
  rw [hcop.card_divisors_mul]
  congr 1
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

-- Helper: for t with all prime factors ≥ 11, d(t)^3 ≤ t
private lemma d_cube_le_of_large_primes :
    ∀ t : ℕ, (∀ p, p.Prime → p ∣ t → 11 ≤ p) → t.divisors.card ^ 3 ≤ t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    by_cases ht0 : t ≤ 1
    · interval_cases t <;> simp
    · push_neg at ht0
      set p := t.minFac with hp_def
      have hp_prime : p.Prime := Nat.minFac_prime (by omega)
      have hp_dvd : p ∣ t := Nat.minFac_dvd t
      have hp_ge : 11 ≤ p := ht p hp_prime hp_dvd
      obtain ⟨e, m, hm_ndvd, ht_eq⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd (by omega : t ≠ 0) p hp_prime.ne_one
      have he_pos : 1 ≤ e := by
        by_contra h; push_neg at h; interval_cases e
        simp at ht_eq; exact hm_ndvd (ht_eq ▸ hp_dvd)
      have hm_pos : 0 < m := by
        by_contra h; push_neg at h; interval_cases m; simp at ht_eq; omega
      have hdt : t.divisors.card = (e + 1) * m.divisors.card := by
        rw [ht_eq]; exact card_div_prime_pow_mul p m e hp_prime hm_ndvd
      -- Reduce: d(t/p)^3 ≤ t/p by IH, then scale up
      have ht_div_p : t / p = p ^ (e - 1) * m := by
        rw [ht_eq]
        conv_lhs => rw [show p ^ e = p ^ (e - 1) * p from by
          rw [← pow_succ]; congr 1; omega]
        rw [mul_comm (p ^ (e - 1)) p, mul_assoc, Nat.mul_div_cancel_left _ hp_prime.pos]
      have hdt_div_p : (t / p).divisors.card = e * m.divisors.card := by
        rw [ht_div_p]
        have h := card_div_prime_pow_mul p m (e - 1) hp_prime hm_ndvd
        rw [show e - 1 + 1 = e from by omega] at h; exact h
      have h_tp_lt : t / p < t := Nat.div_lt_self (by omega) hp_prime.one_lt
      have h_tp_primes : ∀ q, q.Prime → q ∣ (t / p) → 11 ≤ q :=
        fun q hq hqdvd => ht q hq (dvd_trans hqdvd (Nat.div_dvd_of_dvd hp_dvd))
      have h_ih : (t / p).divisors.card ^ 3 ≤ t / p := ih (t / p) h_tp_lt h_tp_primes
      rw [hdt_div_p, ht_div_p, mul_pow] at h_ih
      rw [hdt, ht_eq, mul_pow]
      -- Key: (e+1)^3 ≤ e^3 * p for p ≥ 11, e ≥ 1
      have hep : (e + 1) ^ 3 ≤ e ^ 3 * p := by
        calc (e + 1) ^ 3 ≤ (2 * e) ^ 3 := by
              apply Nat.pow_le_pow_left; omega
          _ = 8 * e ^ 3 := by ring
          _ ≤ p * e ^ 3 := Nat.mul_le_mul_right _ (by omega)
          _ = e ^ 3 * p := by ring
      calc (e + 1) ^ 3 * m.divisors.card ^ 3
          ≤ (e ^ 3 * p) * m.divisors.card ^ 3 := Nat.mul_le_mul_right _ hep
        _ = p * (e ^ 3 * m.divisors.card ^ 3) := by ring
        _ ≤ p * (p ^ (e - 1) * m) := Nat.mul_le_mul_left _ h_ih
        _ = p ^ e * m := by
            have pe : p * p ^ (e - 1) = p ^ e := by
              obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
              simp only [Nat.add_sub_cancel]; rw [pow_succ, mul_comm p]
            rw [← mul_assoc, pe]

-- The key inequality: d(n)^3 * 2520 ≤ 110592 * n for all positive n.
-- Proof: strip factors of 2,3,5,7, use per-prime bounds, multiply.
-- 35 * d(n)^3 ≤ 1536 * n, then * 72 gives the result (2520 = 35*72, 110592 = 1536*72).
private lemma key_ineq (n : ℕ) (hn : 0 < n) :
    (Nat.divisors n).card ^ 3 * 2520 ≤ 110592 * n := by
  -- Decompose n = 2^a * n₁ with 2 ∤ n₁
  obtain ⟨a, n₁, h2_ndvd, hn_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 (by norm_num)
  have hn₁_pos : 0 < n₁ := by
    by_contra h; push_neg at h; interval_cases n₁; simp at hn_eq; omega
  -- Decompose n₁ = 3^b * n₂ with 3 ∤ n₂
  obtain ⟨b, n₂, h3_ndvd, hn1_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n₁ ≠ 0) 3 (by norm_num)
  have hn₂_pos : 0 < n₂ := by
    by_contra h; push_neg at h; interval_cases n₂; simp at hn1_eq; omega
  -- Decompose n₂ = 5^c * n₃ with 5 ∤ n₃
  obtain ⟨c, n₃, h5_ndvd, hn2_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n₂ ≠ 0) 5 (by norm_num)
  have hn₃_pos : 0 < n₃ := by
    by_contra h; push_neg at h; interval_cases n₃; simp at hn2_eq; omega
  -- Decompose n₃ = 7^d * t with 7 ∤ t
  obtain ⟨d, t, h7_ndvd, hn3_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n₃ ≠ 0) 7 (by norm_num)
  have ht_pos : 0 < t := by
    by_contra h; push_neg at h; interval_cases t; simp at hn3_eq; omega
  -- Divisibility chains for propagating non-divisibility
  have ht_dvd_n3 : t ∣ n₃ := by rw [hn3_eq]; exact dvd_mul_left t _
  have hn3_dvd_n2 : n₃ ∣ n₂ := by rw [hn2_eq]; exact dvd_mul_left n₃ _
  have hn2_dvd_n1 : n₂ ∣ n₁ := by rw [hn1_eq]; exact dvd_mul_left n₂ _
  -- t has no small prime factors
  have h2t : ¬ (2 : ℕ) ∣ t :=
    fun h => h2_ndvd (dvd_trans h (dvd_trans ht_dvd_n3 (dvd_trans hn3_dvd_n2 hn2_dvd_n1)))
  have h3t : ¬ (3 : ℕ) ∣ t :=
    fun h => h3_ndvd (dvd_trans h (dvd_trans ht_dvd_n3 hn3_dvd_n2))
  have h5t : ¬ (5 : ℕ) ∣ t :=
    fun h => h5_ndvd (dvd_trans h ht_dvd_n3)
  -- All prime factors of t are ≥ 11
  have ht_large : ∀ p, p.Prime → p ∣ t → 11 ≤ p := by
    intro p hp hpt
    rcases Nat.lt_or_ge p 11 with hlt | hge
    · have := hp.two_le
      interval_cases p
      all_goals first
        | exact absurd hpt h2t
        | exact absurd hpt h3t
        | exact absurd hpt h5t
        | exact absurd hpt h7_ndvd
        | exact absurd hp (by decide)
    · exact hge
  -- d(t)^3 ≤ t
  have hdt := d_cube_le_of_large_primes t ht_large
  -- 2 ∤ n₂ (since n₂ | n₁ and 2 ∤ n₁)
  have h2_ndvd₂ : ¬ (2 : ℕ) ∣ n₂ := fun h => h2_ndvd (dvd_trans h hn2_dvd_n1)
  -- 2 ∤ n₃, 3 ∤ n₃
  have h2_ndvd₃ : ¬ (2 : ℕ) ∣ n₃ := fun h => h2_ndvd (dvd_trans h (dvd_trans hn3_dvd_n2 hn2_dvd_n1))
  have h3_ndvd₃ : ¬ (3 : ℕ) ∣ n₃ := fun h => h3_ndvd (dvd_trans h hn3_dvd_n2)
  -- d(n) = (a+1)(b+1)(c+1)(d+1) * d(t)
  have hdn : n.divisors.card = (a + 1) * n₁.divisors.card := by
    rw [hn_eq]; exact card_div_prime_pow_mul 2 n₁ a (by norm_num) h2_ndvd
  have hdn₁ : n₁.divisors.card = (b + 1) * n₂.divisors.card := by
    rw [hn1_eq]; exact card_div_prime_pow_mul 3 n₂ b (by norm_num) h3_ndvd
  have hdn₂ : n₂.divisors.card = (c + 1) * n₃.divisors.card := by
    rw [hn2_eq]; exact card_div_prime_pow_mul 5 n₃ c (by norm_num) h5_ndvd
  have hdn₃ : n₃.divisors.card = (d + 1) * t.divisors.card := by
    rw [hn3_eq]; exact card_div_prime_pow_mul 7 t d (by norm_num) h7_ndvd
  have hd_full : n.divisors.card =
      (a + 1) * (b + 1) * (c + 1) * (d + 1) * t.divisors.card := by
    rw [hdn, hdn₁, hdn₂, hdn₃]; ring
  -- n = 2^a * 3^b * 5^c * 7^d * t
  have hn_full : n = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * t := by
    rw [hn_eq, hn1_eq, hn2_eq, hn3_eq]; ring
  -- Per-prime bounds
  have hb2 := bound_prime2 a    -- (a+1)^3 ≤ 8 * 2^a
  have hb3 : (b + 1) ^ 3 ≤ 3 * 3 ^ b := by
    calc (b + 1) ^ 3 ≤ 3 ^ (b + 1) := bound_prime3 b
      _ = 3 * 3 ^ b := by rw [pow_succ, mul_comm]
  have hb5 := bound_prime5 c    -- 5 * (c+1)^3 ≤ 8 * 5^c
  have hb7 := bound_prime7 d    -- 7 * (d+1)^3 ≤ 8 * 7^d
  -- Main calculation: 35 * d(n)^3 ≤ 1536 * n
  -- Then d(n)^3 * 2520 = 72 * (35 * d(n)^3) ≤ 72 * 1536 * n = 110592 * n
  suffices h35 : 35 * n.divisors.card ^ 3 ≤ 1536 * n by
    calc n.divisors.card ^ 3 * 2520
        = 72 * (35 * n.divisors.card ^ 3) := by ring
      _ ≤ 72 * (1536 * n) := by linarith
      _ = 110592 * n := by ring
  calc 35 * n.divisors.card ^ 3
      = (a + 1) ^ 3 * (b + 1) ^ 3 * (5 * (c + 1) ^ 3) *
        (7 * (d + 1) ^ 3) * t.divisors.card ^ 3 := by
          rw [hd_full]; ring
    _ ≤ (8 * 2 ^ a) * (3 * 3 ^ b) * (8 * 5 ^ c) *
        (8 * 7 ^ d) * t := by
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          · exact Nat.mul_le_mul hb2 hb3
          · exact hb5
          · exact hb7
          exact hdt
    _ = 1536 * n := by rw [hn_full]; ring

-- The main theorem
theorem amc12a_2021_p25
  (N : ℕ)
  (hN : 0 < N)
  (f : ℕ → ℝ)
  (h₀ : ∀ n, 0 < n → f n = ((Nat.divisors n).card)/(n^((1:ℝ)/3)))
  (h₁ : ∀ n ≠ N, 0 < n → f n < f N) :
  (Nat.digits 10 N).sum = 9 := by
  have hN2520 : N = 2520 := by
    by_contra hne
    have h2520pos : (0 : ℕ) < 2520 := by norm_num
    have hf_lt := h₁ 2520 (Ne.symm hne) h2520pos
    have hfN := h₀ N hN
    have hf2520 := h₀ 2520 h2520pos
    have hd2520 : (Nat.divisors 2520).card = 48 := by native_decide
    rw [hfN, hf2520, hd2520] at hf_lt
    have hkey := key_ineq N hN
    have hkey_real : ((Nat.divisors N).card : ℝ) ^ 3 * 2520 ≤ 110592 * (N : ℝ) := by
      exact_mod_cast hkey
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hN13pos : (0 : ℝ) < (N : ℝ) ^ ((1:ℝ)/3) := rpow_pos_of_pos hNpos _
    have h2520rpos : (0 : ℝ) < (2520 : ℝ) := by norm_num
    have h252013pos : (0 : ℝ) < (2520 : ℝ) ^ ((1:ℝ)/3) := rpow_pos_of_pos h2520rpos _
    have hf_lt' : (48 : ℝ) * (N : ℝ) ^ ((1:ℝ)/3) <
        ((Nat.divisors N).card : ℝ) * (2520 : ℝ) ^ ((1:ℝ)/3) := by
      have h1 := (div_lt_div_iff₀ h252013pos hN13pos).mp hf_lt
      simp only [Nat.cast_ofNat] at h1; exact h1
    have hcube : (48 * (N : ℝ) ^ ((1:ℝ)/3)) ^ 3 <
        (((Nat.divisors N).card : ℝ) * (2520 : ℝ) ^ ((1:ℝ)/3)) ^ 3 :=
      pow_lt_pow_left₀ hf_lt' (by positivity) (by norm_num)
    rw [mul_pow, mul_pow] at hcube
    have hN13_cube : ((N : ℝ) ^ ((1:ℝ)/3)) ^ 3 = (N : ℝ) := by
      rw [← rpow_natCast ((N : ℝ) ^ ((1:ℝ)/3)) 3, ← rpow_mul (le_of_lt hNpos)]; norm_num
    have h2520_13_cube : ((2520 : ℝ) ^ ((1:ℝ)/3)) ^ 3 = (2520 : ℝ) := by
      rw [← rpow_natCast ((2520 : ℝ) ^ ((1:ℝ)/3)) 3, ← rpow_mul (le_of_lt h2520rpos)]; norm_num
    rw [hN13_cube, h2520_13_cube] at hcube
    have h48cubed : (48 : ℝ) ^ 3 = 110592 := by norm_num
    rw [h48cubed] at hcube; linarith
  subst hN2520; native_decide
