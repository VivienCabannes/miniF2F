import Mathlib

open BigOperators Real Nat Topology Rat

private lemma succ_pow4_le (k : ℕ) (hk : 17 ≤ k) : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by
  have : k = (k - 17) + 17 := by omega; rw [this]
  nlinarith [sq_nonneg (k - 17), sq_nonneg ((k - 17) * ((k - 17) + 32))]

private lemma two_pow_gt_pow4 (n : ℕ) (hn : 17 ≤ n) : n ^ 4 < 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : 17 ≤ k
    · calc (k + 1) ^ 4 ≤ 2 * k ^ 4 := succ_pow4_le k hk
        _ < 2 * 2 ^ k := by linarith [ih hk]; _ = 2 ^ (k + 1) := by ring
    · have : k = 16 := by omega; subst this; norm_num

private lemma succ_pow9_le (k : ℕ) (hk : 28 ≤ k) : (k + 1) ^ 9 ≤ 3 * k ^ 9 := by
  have : k = (k - 28) + 28 := by omega; rw [this]
  nlinarith [sq_nonneg (k - 28), sq_nonneg ((k - 28)^2), sq_nonneg ((k - 28)^3),
             sq_nonneg ((k - 28)^4), sq_nonneg ((k - 28) * ((k - 28) + 1)),
             mul_self_nonneg ((k - 28)^2 + 28*(k - 28) : ℕ)]

private lemma three_pow_gt_pow9 (n : ℕ) (hn : 28 ≤ n) : n ^ 9 < 3 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : 28 ≤ k
    · calc (k + 1) ^ 9 ≤ 3 * k ^ 9 := succ_pow9_le k hk
        _ < 3 * 3 ^ k := by linarith [ih hk]; _ = 3 ^ (k + 1) := by ring
    · have : k = 27 := by omega; subst this; norm_num

-- k * y² ≠ y^k for y ≥ 4, k ≥ 1
private lemma mul_sq_ne_pow (y k : ℕ) (hy : 4 ≤ y) (hk : 1 ≤ k) : k * y ^ 2 ≠ y ^ k := by
  intro heq
  by_cases hk5 : k ≤ 4
  · interval_cases k
    · simp at heq; nlinarith
    · nlinarith [sq_nonneg y]
    · have : y^2 * (y - 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h; · nlinarith [sq_nonneg y]; · omega
    · have : y^2 * (y^2 - 4) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h; · nlinarith [sq_nonneg y]
      · nlinarith [sq_nonneg (y - 2)]
  · push_neg at hk5
    have : k < 4 ^ (k - 2) := by
      induction k with
      | zero => omega
      | succ n ih =>
        by_cases hn : 5 ≤ n
        · calc n + 1 ≤ 4 * n := by omega
            _ < 4 * 4 ^ (n - 2) := by nlinarith [ih (by omega)]
            _ = 4 ^ (n - 2 + 1) := by ring
            _ = 4 ^ (n + 1 - 2) := by congr 1; omega
        · interval_cases n <;> norm_num
    have hlt : k * y ^ 2 < y ^ k := by
      calc k * y ^ 2 < y ^ (k - 2) * y ^ 2 :=
            Nat.mul_lt_mul_of_pos_right
              (lt_of_lt_of_le this (Nat.pow_le_pow_left (by omega) _)) (by positivity)
        _ = y ^ k := by rw [← pow_add]; congr 1; omega
    linarith

-- Helper: from d ∣ n (both nonzero), d.factorization p ≤ n.factorization p
private lemma factorization_le_of_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) (h : d ∣ n)
    (p : ℕ) : d.factorization p ≤ n.factorization p :=
  (Nat.factorization_le_iff_dvd hd hn).mpr h p

-- Helper: from c^k | d^k (both bases nonzero, k > 0), derive c | d
private lemma dvd_of_pow_dvd_pow {c d k : ℕ} (hc : 0 < c) (hd : 0 < d) (hk : 0 < k)
    (h : c ^ k ∣ d ^ k) : c ∣ d := by
  rw [← Nat.factorization_le_iff_dvd (by omega) (by omega)]
  intro p
  by_cases hpc : c.factorization p = 0
  · simp [hpc]
  · have hpne : p.Prime := by
      by_contra hp
      exact hpc (Nat.factorization_eq_zero_of_non_prime c hp)
    have hle : (c ^ k).factorization p ≤ (d ^ k).factorization p :=
      factorization_le_of_dvd (by positivity) (by positivity) h p
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hle
    exact Nat.le_of_mul_le_mul_left hle hk

theorem imo_1997_p5
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x^(y^2) = y^x) :
  (x, y) = (1, 1) ∨ (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  obtain ⟨hx, hy⟩ := h₀
  have hxne : x ≠ 0 := by omega
  have hyne : y ≠ 0 := by omega
  have hfact : ∀ p, y ^ 2 * x.factorization p = x * y.factorization p := by
    intro p
    have : (x ^ (y ^ 2)).factorization p = (y ^ x).factorization p := by rw [h₁]
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at this; linarith
  have hsame : ∀ p, p.Prime → (p ∣ x ↔ p ∣ y) := by
    intro p hp; constructor
    · intro hpx; by_contra hpy
      have := hp.factorization_pos_of_dvd hxne hpx
      have h0 : y.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpy
      have := hfact p; rw [h0, mul_zero] at this
      rcases mul_eq_zero.mp this with h | h <;> [nlinarith [sq_nonneg y]; omega]
    · intro hpy; by_contra hpx
      have := hp.factorization_pos_of_dvd hyne hpy
      have h0 : x.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpx
      have := hfact p; rw [h0, mul_zero] at this
      rcases mul_eq_zero.mp this.symm with h | h <;> omega
  have hcross : ∀ p q, x.factorization p * y.factorization q =
      x.factorization q * y.factorization p := fun p q => by nlinarith [hfact p, hfact q]
  have hy3 : y ≤ 3 := by
    by_contra h; push_neg at h; have h4 : 4 ≤ y := by omega
    have hx2 : 2 ≤ x := by
      by_contra h1; push_neg at h1; interval_cases x; simp at h₁; omega
    set p₀ := y.minFac
    have hp₀ : p₀.Prime := Nat.minFac_prime (by omega)
    set a := y.factorization p₀; set b := x.factorization p₀
    have ha : 0 < a := hp₀.factorization_pos_of_dvd hyne (Nat.minFac_dvd y)
    have hb : 0 < b := hp₀.factorization_pos_of_dvd hxne ((hsame p₀ hp₀).mpr (Nat.minFac_dvd y))
    -- x^a = y^b (from factorization)
    have hpow : x ^ a = y ^ b := by
      apply Nat.factorization_inj (by positivity) (by positivity)
      simp only [Nat.factorization_pow]; ext p
      simp [Finsupp.smul_apply, smul_eq_mul]; exact hcross p₀ p
    -- y² * b = x * a
    have hab : y ^ 2 * b = x * a := hfact p₀
    -- KEY: y^(2a) * b^a = y^b * a^a
    have hkey : y ^ (2 * a) * b ^ a = y ^ b * a ^ a := by
      have h1 : (y ^ 2 * b) ^ a = y ^ b * a ^ a := by
        rw [hab, mul_pow, mul_comm (x ^ a), hpow]
      calc y ^ (2 * a) * b ^ a = (y ^ 2) ^ a * b ^ a := by ring
        _ = (y ^ 2 * b) ^ a := by rw [mul_pow]
        _ = y ^ b * a ^ a := h1
    -- Case split on b vs 2a
    by_cases hba : 2 * a ≤ b
    · -- b ≥ 2a: derive a^a | b^a, then a | b
      have hge : y ^ (2 * a) * (y ^ (b - 2 * a) * a ^ a) = y ^ (2 * a) * b ^ a := by
        rw [← mul_assoc, ← pow_add]; congr 1; omega; exact hkey.symm
      have heq : y ^ (b - 2 * a) * a ^ a = b ^ a :=
        Nat.eq_of_mul_eq_left (by positivity) hge
      -- a^a | b^a
      have hdvd : a ^ a ∣ b ^ a := ⟨y ^ (b - 2 * a), heq.symm⟩
      -- a | b (from a^a | b^a using factorization)
      have hab_dvd : a ∣ b := dvd_of_pow_dvd_pow ha hb ha hdvd
      -- Let m = b/a.
      set m := b / a with hm_def
      have hba_eq : b = a * m := (Nat.div_mul_cancel hab_dvd).symm
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hba_eq; omega
        · exact h
      -- x = y^2 * m
      have hxm : x = y ^ 2 * m := by
        have := hab; rw [hba_eq] at this
        have : y ^ 2 * (a * m) = x * a := this
        nlinarith [Nat.eq_of_mul_eq_right (by omega : 0 < a) (by linarith : x * a = y ^ 2 * m * a)]
      -- y^(2a) * m^a = y^(am)
      have hpow2 : y ^ (2 * a) * m ^ a = y ^ (a * m) := by
        have : (y ^ 2 * m) ^ a = y ^ (a * m) := by
          rw [← hxm, ← hba_eq]; exact hpow
        calc y ^ (2 * a) * m ^ a = (y ^ 2) ^ a * m ^ a := by ring
          _ = (y ^ 2 * m) ^ a := by rw [mul_pow]
          _ = y ^ (a * m) := this
      -- Case m = 1: y^(2a) = y^a, so 2a = a, contradiction with a > 0.
      rcases m.eq_or_gt with rfl | hm2
      · -- m = 0: impossible since m > 0
        omega
      rcases eq_or_lt_of_le hm2 with rfl | hm2
      · -- m = 1
        simp at hpow2
        have : 2 * a = a * 1 :=
          Nat.pow_right_injective (by omega : 2 ≤ y) hpow2
        omega
      · -- m ≥ 2
        have ham : a * m = 2 * a + a * (m - 2) := by omega
        rw [ham] at hpow2
        have : y ^ (2 * a) * m ^ a = y ^ (2 * a) * y ^ (a * (m - 2)) := by
          rw [← pow_add]; exact hpow2
        have : m ^ a = y ^ (a * (m - 2)) :=
          Nat.eq_of_mul_eq_left (by positivity) this
        have hma : a * (m - 2) = (m - 2) * a := by ring
        rw [hma] at this
        have : m ^ a = (y ^ (m - 2)) ^ a := by rw [← pow_mul]; exact this
        have hm_eq : m = y ^ (m - 2) := by
          exact Nat.pow_left_injective (by omega : 0 < a) |>.eq_iff.mp this
        have : m * y ^ 2 = y ^ m := by
          rw [hm_eq, ← pow_add]; congr 1; omega
        exact mul_sq_ne_pow y m h4 (by omega) this
    · -- b < 2a
      push_neg at hba
      have hab2 : 2 * a = b + (2 * a - b) := by omega
      rw [hab2] at hkey
      rw [pow_add] at hkey
      have heq2 : y ^ (2 * a - b) * b ^ a = a ^ a :=
        Nat.eq_of_mul_eq_left (by positivity) (by linarith)
      -- b^a | a^a
      have hdvd2 : b ^ a ∣ a ^ a := ⟨y ^ (2 * a - b), heq2.symm⟩
      -- b | a
      have hba_dvd : b ∣ a := dvd_of_pow_dvd_pow hb ha ha hdvd2
      -- Let r = a/b.
      set r := a / b with hr_def
      have hab_eq : a = b * r := (Nat.div_mul_cancel hba_dvd).symm
      have hr_pos : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · rw [h, mul_zero] at hab_eq; omega
        · exact h
      -- y^2 = x * r
      have hxr : x * r = y ^ 2 := by
        have := hab; rw [hab_eq] at this
        nlinarith [Nat.eq_of_mul_eq_right (by omega : 0 < b) (by linarith : y ^ 2 * b = x * r * b)]
      -- y^(b*(2r-1)) = r^(b*r) (from heq2 after substitution)
      have h2a : 2 * a - b = b * (2 * r - 1) := by rw [hab_eq]; omega
      have hpow3 : y ^ (b * (2 * r - 1)) = r ^ (b * r) := by
        have hmul : (b * r) ^ (b * r) = b ^ (b * r) * r ^ (b * r) := by rw [mul_pow]
        rw [h2a, hab_eq] at heq2
        rw [hmul] at heq2
        have heq3 : b ^ (b * r) * y ^ (b * (2 * r - 1)) = b ^ (b * r) * r ^ (b * r) := by
          linarith
        exact Nat.eq_of_mul_eq_left (by positivity) heq3
      -- (y^(2r-1))^b = (r^r)^b
      have hpow4 : (y ^ (2 * r - 1)) ^ b = (r ^ r) ^ b := by
        rw [← pow_mul, ← pow_mul]
        convert hpow3 using 2 <;> ring
      -- y^(2r-1) = r^r
      have hyr : y ^ (2 * r - 1) = r ^ r :=
        Nat.pow_left_injective (by omega) |>.eq_iff.mp hpow4
      -- Case r = 1: y = 1, contradiction with y ≥ 4.
      by_cases hr1 : r = 1
      · -- r = 1: y^1 = 1^1 = 1, contradiction
        rw [hr1] at hyr; simp at hyr; omega
      · -- r ≥ 2: derive contradiction from y^(2r-1) = r^r using p-adic valuation
        have hr2 : 2 ≤ r := by omega
        have hr1' : r ≠ 1 := by omega
        set q := r.minFac with hq_def
        have hq : q.Prime := Nat.minFac_prime hr1'
        have hqdvr : q ∣ r := Nat.minFac_dvd r
        -- (2r-1) * v_q(y) = r * v_q(r) from comparing factorizations
        have hvq : (2 * r - 1) * y.factorization q = r * r.factorization q := by
          have h := congr_arg (fun n => n.factorization q) hyr
          simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h
          exact h
        -- v_q(r) ≥ 1
        have hvqr : 0 < r.factorization q := hq.factorization_pos_of_dvd (by omega) hqdvr
        -- gcd(2r-1, r) = 1
        have hcop_r : Nat.Coprime (2 * r - 1) r := by
          have h_sub : 2 * r - 1 - r = r - 1 := by omega
          have h_le : r ≤ 2 * r - 1 := by omega
          rw [← Nat.coprime_sub_self_left h_le, h_sub]
          exact ((Nat.coprime_self_sub_right (by omega : 1 ≤ r)).mpr
            ((Nat.coprime_one_right_iff r).mpr trivial)).symm
        -- (2r-1) | v_q(r)
        have hdvd_vq : (2 * r - 1) ∣ r.factorization q := by
          have : (2 * r - 1) ∣ r * r.factorization q := by
            rw [← hvq]; exact dvd_mul_right _ _
          exact hcop_r.dvd_of_dvd_mul_left this
        -- v_q(r) < 2r - 1: since q^v_q(r) | r and q ≥ 2, we get 2^v_q(r) ≤ r, hence v_q(r) < r < 2r-1
        have hvq_bound : r.factorization q < 2 * r - 1 := by
          have h1 : q ^ r.factorization q ∣ r := Nat.ordProj_dvd r q
          have h2 : q ^ r.factorization q ≤ r := Nat.le_of_dvd (by omega) h1
          have hq2 : 2 ≤ q := hq.two_le
          have h3 : 2 ^ r.factorization q ≤ r :=
            le_trans (pow_le_pow_left' hq2 _) h2
          -- 2^n ≤ r and r ≥ 2 implies n < r (since n < 2^n ≤ r)
          have h4 : r.factorization q < r := by
            calc r.factorization q < 2 ^ r.factorization q := Nat.lt_two_pow_self
              _ ≤ r := h3
          omega
        -- (2r-1) | v_q(r) and v_q(r) ≥ 1 and v_q(r) < 2r-1: contradiction
        have := Nat.le_of_dvd (by omega) hdvd_vq
        omega
  interval_cases y
  · simp at h₁; left; exact Prod.ext h₁ rfl
  · have h2 : x ^ 4 = 2 ^ x := by simpa using h₁
    have hxle : x ≤ 16 := by
      by_contra h; push_neg at h; linarith [two_pow_gt_pow4 x (by omega)]
    interval_cases x <;> simp_all
  · have h3 : x ^ 9 = 3 ^ x := by simpa using h₁
    have hxle : x ≤ 27 := by
      by_contra h; push_neg at h; linarith [three_pow_gt_pow9 x (by omega)]
    interval_cases x <;> simp_all
