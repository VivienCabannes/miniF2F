import Mathlib

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

private lemma vieta_descent (k : ℕ) (a b : ℕ) (hk : a ^ 2 + b ^ 2 = (a * b + 1) * k) :
    ∃ x : ℕ, x ^ 2 = k := by
  induction h : a + b using Nat.strongRecOn generalizing a b with
  | ind n ih =>
  by_cases hb : b = 0
  · subst hb; simp at hk; exact ⟨a, hk⟩
  by_cases ha : a = 0
  · subst ha; simp at hk; exact ⟨b, hk⟩
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
  have hk_pos : 0 < k := by
    by_contra hk0; push_neg at hk0; interval_cases k; simp at hk; omega
  rcases le_or_gt b a with hab | hab
  · have ha'_nonneg : (0 : ℤ) ≤ (k : ℤ) * b - a := by
      by_contra h_neg; push_neg at h_neg
      set a' : ℤ := (k : ℤ) * b - a
      have quad' : a' ^ 2 + (b : ℤ) ^ 2 = (k : ℤ) * (a' * b + 1) := by
        zify at hk; nlinarith
      have hab' : a' * (b : ℤ) + 1 ≤ 0 := by nlinarith
      have hle : (k : ℤ) * (a' * b + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hab'
      nlinarith [sq_nonneg a', sq_nonneg (b : ℤ)]
    obtain ⟨a'_n, ha'_eq⟩ : ∃ m : ℕ, (m : ℤ) = (k : ℤ) * b - a :=
      ⟨((k : ℤ) * b - a).toNat, by omega⟩
    have hk' : a'_n ^ 2 + b ^ 2 = (a'_n * b + 1) * k := by
      zify; nlinarith [ha'_eq, hk]
    have h_smaller : a'_n + b < a + b := by
      have prod : (a : ℤ) * a'_n = (b : ℤ) ^ 2 - k := by zify at hk; nlinarith [ha'_eq]
      have h1 : (a : ℤ) * a'_n < a * b := by nlinarith
      have : (a'_n : ℤ) < b := by
        rcases eq_or_lt_of_le (show (0 : ℤ) ≤ a'_n from by positivity) with h0 | h0
        · omega
        · exact lt_of_mul_lt_mul_of_nonneg_left h1 (by positivity)
      omega
    exact ih (a'_n + b) (by omega) a'_n b hk' rfl
  · have ha'_nonneg : (0 : ℤ) ≤ (k : ℤ) * a - b := by
      by_contra h_neg; push_neg at h_neg
      set b' : ℤ := (k : ℤ) * a - b
      have quad' : b' ^ 2 + (a : ℤ) ^ 2 = (k : ℤ) * (b' * a + 1) := by
        zify at hk; nlinarith
      have hab' : b' * (a : ℤ) + 1 ≤ 0 := by nlinarith
      have hle : (k : ℤ) * (b' * a + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hab'
      nlinarith [sq_nonneg b', sq_nonneg (a : ℤ)]
    obtain ⟨b'_n, hb'_eq⟩ : ∃ m : ℕ, (m : ℤ) = (k : ℤ) * a - b :=
      ⟨((k : ℤ) * a - b).toNat, by omega⟩
    have hk' : b'_n ^ 2 + a ^ 2 = (b'_n * a + 1) * k := by
      zify; nlinarith [hb'_eq, hk]
    have h_smaller : a + b'_n < a + b := by
      have prod : (b : ℤ) * b'_n = (a : ℤ) ^ 2 - k := by zify at hk; nlinarith [hb'_eq]
      have h1 : (b : ℤ) * b'_n < b * a := by nlinarith
      have : (b'_n : ℤ) < a := by
        rcases eq_or_lt_of_le (show (0 : ℤ) ≤ b'_n from by positivity) with h0 | h0
        · omega
        · exact lt_of_mul_lt_mul_of_nonneg_left h1 (by positivity)
      omega
    have hk'' : a ^ 2 + b'_n ^ 2 = (a * b'_n + 1) * k := by linarith [hk']
    exact ih (a + b'_n) (by omega) a b'_n hk'' (by omega)

theorem imo_1988_p6 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a * b + 1 ∣ a ^ 2 + b ^ 2) :
  ∃ x : ℕ, (x ^ 2 : ℝ) = (a ^ 2 + b ^ 2) / (a * b + 1) := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨x, hx⟩ := vieta_descent k a b hk
  refine ⟨x, ?_⟩
  have hab_pos : (0 : ℝ) < (a : ℝ) * b + 1 := by positivity
  rw [eq_div_iff (ne_of_gt hab_pos)]
  have : (x ^ 2 : ℝ) * ((a : ℝ) * b + 1) = ((x ^ 2 * (a * b + 1) : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  have : ((a ^ 2 + b ^ 2 : ℕ) : ℝ) = (a : ℝ) ^ 2 + b ^ 2 := by push_cast; ring
  rw [← this]
  congr 1
  rw [hx]; linarith
