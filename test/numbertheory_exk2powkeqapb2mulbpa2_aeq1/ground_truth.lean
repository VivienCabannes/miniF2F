import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 1600000

-- Helper: if n * (n+1) = 2^k and n > 0, then n = 1
private lemma eq_one_of_mul_succ_eq_two_pow {n k : ℕ} (hn : 0 < n)
    (h : n * (n + 1) = 2 ^ k) : n = 1 := by
  have hn_dvd : n ∣ 2 ^ k := ⟨n + 1, h.symm⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn_dvd
  have hn1_dvd : (2^i + 1) ∣ 2 ^ k := ⟨2^i, by linarith⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn1_dvd
  by_contra hi
  have hi0 : i ≠ 0 := fun h0 => hi (by simp [h0])
  -- 2^i + 1 = 2^j, so 2^j - 2^i = 1
  -- For i ≥ 1: 2 | 2^i and 2 | 2^j (for j ≥ 1), so 2 | (2^j - 2^i) = 1, contradiction
  -- For j = 0: 2^i + 1 = 1, so 2^i = 0, impossible
  rcases j with _ | j
  · simp at hj
  · -- j ≥ 1: 2^i + 1 = 2^(j+1), both sides ≥ 3
    -- 2 | 2^(j+1) and 2 | 2^i, so 2 | 1, contradiction
    have h2i : 2 ∣ 2 ^ i := ⟨2 ^ (i-1), by
      conv_lhs => rw [show i = (i - 1) + 1 from by omega, pow_succ]
      exact (mul_comm _ _).symm⟩
    have h2j : 2 ∣ 2 ^ (j + 1) := ⟨2 ^ j, by ring⟩
    have h_sub : 2 ∣ (2 ^ (j + 1) - 2 ^ i) := Nat.dvd_sub h2j h2i
    have h_one : 2 ^ (j + 1) - 2 ^ i = 1 := by omega
    rw [h_one] at h_sub
    exact absurd h_sub (by omega)

-- Helper: b^2 % 2 = b % 2 for natural numbers
private lemma sq_mod_two (b : ℕ) : b ^ 2 % 2 = b % 2 := by
  have : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases this with h | h
  · have hb_even : 2 ∣ b := Nat.dvd_of_mod_eq_zero h
    obtain ⟨c, rfl⟩ := hb_even
    simp [mul_pow]; omega
  · have hb_odd : ¬ 2 ∣ b := by omega
    have : ¬ 2 ∣ b ^ 2 := mt (fun h2 => (Nat.prime_two.dvd_of_dvd_pow h2)) hb_odd
    omega

-- Core: given a < b with a+b²=2^m, b+a²=2^n, m,n≥1, derive contradiction
private lemma no_lt {a b m n : ℕ} (ha : 0 < a) (_hb : 0 < b)
    (hm : a + b ^ 2 = 2 ^ m) (hn : b + a ^ 2 = 2 ^ n)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hab_lt : a < b) : False := by
  have hm_z : (a : ℤ) + (b : ℤ) ^ 2 = 2 ^ m := by exact_mod_cast hm
  have hn_z : (b : ℤ) + (a : ℤ) ^ 2 = 2 ^ n := by exact_mod_cast hn
  have hdiff : ((b : ℤ) - a) * ((b : ℤ) + a - 1) = 2 ^ m - 2 ^ n := by nlinarith
  -- Same parity: 2 | (a + b^2) means a ≡ b^2 ≡ b (mod 2)
  have hpar : a % 2 = b % 2 := by
    have h1 : 2 ∣ (a + b ^ 2) := by rw [hm]; exact dvd_pow_self 2 (by omega : m ≠ 0)
    have := sq_mod_two b
    omega
  -- b + a - 1 is odd (since a ≡ b mod 2, a + b is even, a + b - 1 is odd)
  have hodd : ¬ (2 : ℤ) ∣ ((b : ℤ) + a - 1) := by
    intro ⟨c, hc⟩
    have hab_even : (a + b) % 2 = 0 := by omega
    omega
  have hba_pos : (0 : ℤ) < (b : ℤ) - a := by omega
  have hmn : n < m := by
    by_contra hmn
    push_neg at hmn
    have h2 : (2 : ℤ) ^ m ≤ 2 ^ n := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) hmn
    have hba1_pos : (0 : ℤ) < (b : ℤ) + a - 1 := by omega
    linarith [mul_pos hba_pos hba1_pos]
  have hfact : (2 : ℤ) ^ m - 2 ^ n = 2 ^ n * ((2 : ℤ) ^ (m - n) - 1) := by
    have : (2 : ℤ) ^ m = 2 ^ n * 2 ^ (m - n) := by
      rw [← pow_add]; congr 1; omega
    linarith
  have hcop : IsCoprime ((b : ℤ) + a - 1) ((2 : ℤ) ^ n) :=
    Int.prime_two.irreducible.coprime_pow_of_not_dvd n hodd
  have hdvd_prod : (2 : ℤ) ^ n ∣ ((b : ℤ) - a) * ((b : ℤ) + a - 1) := by
    rw [hdiff]; exact ⟨2 ^ (m - n) - 1, hfact⟩
  have h2n_dvd_ba : (2 : ℤ) ^ n ∣ ((b : ℤ) - a) :=
    hcop.symm.dvd_of_dvd_mul_right hdvd_prod
  have hba_ge : (2 : ℤ) ^ n ≤ (b : ℤ) - a := Int.le_of_dvd hba_pos h2n_dvd_ba
  linarith [show 0 < (a : ℤ) ^ 2 + (a : ℤ) from by positivity]

theorem numbertheory_exk2powkeqapb2mulbpa2_aeq1
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : ∃ k > 0, 2^k = (a + b^2) * (b + a^2)) :
  a = 1 := by
  obtain ⟨ha, hb⟩ := h₀
  obtain ⟨k, _, heq⟩ := h₁
  have heq' : (a + b^2) * (b + a^2) = 2^k := heq.symm
  have hd1 : (a + b^2) ∣ 2^k := Dvd.intro (b + a^2) heq'
  have hd2 : (b + a^2) ∣ 2^k := Dvd.intro_left (a + b^2) heq'
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  have hm1 : 1 ≤ m := by
    rcases m with _ | m
    · simp at hm; nlinarith
    · omega
  have hn1 : 1 ≤ n := by
    rcases n with _ | n
    · simp at hn; nlinarith
    · omega
  have hab : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · exact (no_lt ha hb hm hn hm1 hn1 h).elim
    · exact h
    · exact (no_lt hb ha hn hm hn1 hm1 h).elim
  subst hab
  have : a * (a + 1) = 2 ^ n := by nlinarith
  exact eq_one_of_mul_succ_eq_two_pow ha this
