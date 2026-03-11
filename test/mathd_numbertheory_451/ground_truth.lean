import Mathlib
import Aesop
set_option maxHeartbeats 400000
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat

lemma round4_divisors_of_pq_7d12b6ea (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    (Nat.divisors (p * q)).card = 4 ∧ (∑ d in Nat.divisors (p * q), d) = 1 + p + q + p * q := by
  have h1 : ∀ (x : ℕ), x ∣ p * q ↔ x = 1 ∨ x = p ∨ x = q ∨ x = p * q := by
    intro x
    constructor
    · intro h_dvd
      by_cases h_px : p ∣ x
      · rcases h_px with ⟨k, rfl⟩
        have hp_pos : 0 < p := Nat.Prime.pos hp
        have h_k_dvd_q : k ∣ q := by
          have h : p * k ∣ p * q := by simpa using h_dvd
          exact Nat.dvd_of_mul_dvd_mul_left hp_pos h
        have h_k_eq_1_or_k_eq_q : k = 1 ∨ k = q := by
          exact Nat.Prime.eq_one_or_self_of_dvd hq k h_k_dvd_q
        cases h_k_eq_1_or_k_eq_q with
        | inl h_k_eq_1 =>
          have h_x_eq_p : p * k = p := by
            rw [h_k_eq_1]
            <;> ring
          exact Or.inr (Or.inl (by linarith))
        | inr h_k_eq_q =>
          have h_x_eq_pq : p * k = p * q := by
            rw [h_k_eq_q]
            <;> ring
          exact Or.inr (Or.inr (Or.inr (by linarith)))
      · have h_coprime : Nat.Coprime x p := by
          have h : Nat.Coprime p x := (Nat.Prime.coprime_iff_not_dvd hp).mpr h_px
          exact h.symm
        have h_x_dvd_q : x ∣ q := by
          apply Nat.Coprime.dvd_of_dvd_mul_right h_coprime
          rw [mul_comm]
          exact h_dvd
        have h_x_eq_1_or_x_eq_q : x = 1 ∨ x = q := by
          exact Nat.Prime.eq_one_or_self_of_dvd hq x h_x_dvd_q
        cases h_x_eq_1_or_x_eq_q with
        | inl h_x_eq_1 =>
          exact Or.inl (by linarith)
        | inr h_x_eq_q =>
          rw [h_x_eq_q]
          <;> simp
    · intro h_x_cases
      rcases h_x_cases with (rfl | rfl | rfl | rfl)
      · simp
      · simp
      · simp
      · simp
  have h2 : Nat.divisors (p * q) = ({1, p, q, p * q} : Finset ℕ) := by
    ext x
    simp only [Nat.mem_divisors, h1]
    <;> aesop
  have h3 : (1 : ℕ) ≠ p := by
    have h31 : 2 ≤ p := Nat.Prime.two_le hp
    linarith
  have h4 : (1 : ℕ) ≠ q := by
    have h41 : 2 ≤ q := Nat.Prime.two_le hq
    linarith
  have h5 : (1 : ℕ) ≠ p * q := by
    have h51 : 2 ≤ p := Nat.Prime.two_le hp
    have h52 : 2 ≤ q := Nat.Prime.two_le hq
    have h53 : 4 ≤ p * q := by nlinarith
    linarith
  have h6 : p ≠ p * q := by
    intro h
    have h61 : p = p * q := by linarith
    have h62 : p > 0 := Nat.Prime.pos hp
    have h63 : q = 1 := by nlinarith
    have h64 : 2 ≤ q := Nat.Prime.two_le hq
    linarith
  have h7 : q ≠ p * q := by
    intro h
    have h71 : q = p * q := by linarith
    have h72 : q > 0 := Nat.Prime.pos hq
    have h73 : p = 1 := by nlinarith
    have h74 : 2 ≤ p := Nat.Prime.two_le hp
    linarith
  have h8 : ({1, p, q, p * q} : Finset ℕ).card = 4 := by
    simp [Finset.card_insert_of_not_mem, Finset.mem_singleton, h3, h4, h5, h6, h7, hne]
    <;> aesop
  have h9 : (∑ d in ({1, p, q, p * q} : Finset ℕ), d) = 1 + p + q + p * q := by
    simp [Finset.sum_insert, Finset.mem_singleton, h3, h4, h5, h6, h7, hne]
    <;> ring
    <;> aesop
  rw [h2]
  exact ⟨h8, h9⟩


lemma round3_exists_m_for_2016_7d12bc08 : ∃ m : ℕ, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = 2016 := by
  use 1509
  have h_1509 : 1509 = 3 * 503 := by norm_num
  have h_prime_3 : Nat.Prime 3 := by norm_num
  have h_prime_503 : Nat.Prime 503 := by norm_num
  have h_ne_3_503 : (3 : ℕ) ≠ 503 := by norm_num
  have h_divs_1509 := round4_divisors_of_pq_7d12b6ea 3 503 h_prime_3 h_prime_503 h_ne_3_503
  rw [h_1509]
  constructor
  · exact h_divs_1509.1
  · have h_sum : (∑ d in Nat.divisors (3 * 503), d) = 1 + 3 + 503 + 3 * 503 := h_divs_1509.2
    norm_num at h_sum ⊢ <;> linarith


lemma round1_2016_in_S (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) :
    2016 ∈ S := by
  have h1 : 2010 ≤ 2016 := by norm_num
  have h2 : 2016 ≤ 2019 := by norm_num
  have h3 : ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = 2016 := round3_exists_m_for_2016_7d12bc08
  have h4 : 2016 ∈ S := by
    rw [h₀]
    exact ⟨h1, h2, h3⟩
  exact h4


lemma round2_sum_divisors_p_cubed_case_empty (p : ℕ) (hp : Nat.Prime p) :
    ¬ (2010 ≤ (∑ i in (Nat.divisors (p^3)), i) ∧ (∑ i in (Nat.divisors (p^3)), i) ≤ 2019) := by
  have h_sum_div : (∑ i in (Nat.divisors (p^3)), i) = 1 + p + p^2 + p^3 := by
    have h₁ : (∑ i in (Nat.divisors (p^3)), i) = ∑ i in Finset.range (3 + 1), p ^ i := by
      simp [Nat.sum_divisors_prime_pow hp]
    rw [h₁]
    simp [Finset.sum_range_succ]
    <;> ring
  rw [h_sum_div]
  by_cases h : p ≤ 11
  · interval_cases p <;> norm_num at hp ⊢ <;> omega
  · have h₆ : p ≥ 13 := by
      have h₇ : p > 11 := by linarith
      have h₈ : p ≥ 2 := Nat.Prime.two_le hp
      by_contra h₁₀
      have h₁₁ : p < 13 := by linarith
      interval_cases p <;> norm_num at hp <;> contradiction
    have h₇ : 1 + p + p ^ 2 + p ^ 3 ≥ 1 + 13 + 13 ^ 2 + 13 ^ 3 := by gcongr <;> nlinarith
    norm_num at h₇ ⊢ <;> omega


lemma round3_h2011_9ccce46a (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2011) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2011 := by
    have h4 : (1 + p) * (1 + q) = 2011 := h
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := by
      use (1 + q)
      <;> ring
    rw [h4] at h5
    exact h5
  have h4 : 1 + p = 1 ∨ 1 + p = 2011 := by
    have h5 : (1 + p) ∣ 2011 := h3
    have h6 : 1 + p ≤ 2011 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h5 ⊢ <;> omega
  rcases h4 with (h4 | h4)
  · linarith
  · have h5 : (1 + 2011) * (1 + q) = 2011 := by
      rw [h4] at h
      linarith
    have h6 : 1 + q = 1 := by linarith
    have hq1 : q = 0 := by linarith
    rw [hq1] at hq
    norm_num at hq <;> contradiction


lemma round3_h2015_9ccce8d4 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2015) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2015 := by
    have h4 : (1 + p) * (1 + q) = 2015 := h
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := by
      use (1 + q)
      <;> ring
    rw [h4] at h5
    exact h5
  have h4 : 1 + p = 5 ∨ 1 + p = 13 ∨ 1 + p = 31 ∨ 1 + p = 65 ∨ 1 + p = 155 ∨ 1 + p = 403 ∨ 1 + p = 2015 := by
    have h5 : 1 + p ≤ 2015 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4)
  · have hp1 : p = 4 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction
  · have hp1 : p = 12 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction
  · have hp1 : p = 30 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction
  · have hp1 : p = 64 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction
  · have hp1 : p = 154 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction
  · have hp1 : p = 402 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction
  · have hp1 : p = 2014 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction


lemma round3_h2017_9ccced02 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2017) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2017 := by
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := dvd_mul_right _ _
    rw [h] at h5
    exact h5
  have h4 : 1 + p = 1 ∨ 1 + p = 2017 := by
    have h5 : 1 + p ≤ 2017 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4)
  · linarith
  · have h5 : 2017 * (1 + q) = 2017 := by linarith
    have h6 : 1 + q = 1 := by linarith
    have hq1 : q = 0 := by linarith
    rw [hq1] at hq
    norm_num at hq <;> contradiction


lemma round3_h2018_9cccf144 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2018) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2018 := by
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := dvd_mul_right _ _
    rw [h] at h5
    exact h5
  have h4 : 1 + p = 1009 ∨ 1 + p = 2018 := by
    have h5 : 1 + p ≤ 2018 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4)
  · have hp1 : p = 1008 := by linarith
    rw [hp1] at hp
    norm_num at hp <;> contradiction
  · have hp1 : p = 2017 := by linarith
    have h5 : 2018 * (1 + q) = 2018 := by linarith
    have h6 : 1 + q = 1 := by linarith
    have hq1 : q = 0 := by linarith
    rw [hq1] at hq
    norm_num at hq <;> contradiction


lemma round3_h2010_9cccf5f4 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2010) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2010 := by
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := dvd_mul_right _ _
    rw [h] at h5
    exact h5
  have h4 : 1 + p = 3 ∨ 1 + p = 5 ∨ 1 + p = 6 ∨ 1 + p = 10 ∨ 1 + p = 15 ∨ 1 + p = 30 ∨ 1 + p = 67 ∨ 1 + p = 134 ∨ 1 + p = 201 ∨ 1 + p = 335 ∨ 1 + p = 402 ∨ 1 + p = 670 ∨ 1 + p = 1005 ∨ 1 + p = 2010 := by
    have h5 : 1 + p ≤ 2010 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4)
  · have hp1 : p = 2 := by linarith
    have h5 : 3 * (1 + q) = 2010 := by linarith
    have h6 : 1 + q = 670 := by linarith
    have hq1 : q = 669 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 4 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 5 := by linarith
    have h5 : 6 * (1 + q) = 2010 := by linarith
    have h6 : 1 + q = 335 := by linarith
    have hq1 : q = 334 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 9 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 14 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 29 := by linarith
    have h5 : 30 * (1 + q) = 2010 := by linarith
    have h6 : 1 + q = 67 := by linarith
    have hq1 : q = 66 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 66 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 133 := by linarith
    have h5 : 134 * (1 + q) = 2010 := by linarith
    have h6 : 1 + q = 15 := by linarith
    have hq1 : q = 14 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 200 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 334 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 401 := by linarith
    have h5 : 402 * (1 + q) = 2010 := by linarith
    have h6 : 1 + q = 5 := by linarith
    have hq1 : q = 4 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 669 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 1004 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 2009 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction


lemma round3_h2012_9cccfa36 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2012) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2012 := by
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := dvd_mul_right _ _
    rw [h] at h5; exact h5
  have h4 : 1 + p = 4 ∨ 1 + p = 503 ∨ 1 + p = 1006 ∨ 1 + p = 2012 := by
    have h5 : 1 + p ≤ 2012 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4 | h4 | h4)
  · have hp1 : p = 3 := by linarith
    have h5 : 4 * (1 + q) = 2012 := by linarith
    have h6 : 1 + q = 503 := by linarith
    have hq1 : q = 502 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 502 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 1005 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 2011 := by linarith
    have h5 : 2012 * (1 + q) = 2012 := by linarith
    have h6 : 1 + q = 1 := by linarith
    have hq1 : q = 0 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction


lemma round3_h2013_9cccfe6e (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2013) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2013 := by
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := dvd_mul_right _ _
    rw [h] at h5; exact h5
  have h4 : 1 + p = 3 ∨ 1 + p = 11 ∨ 1 + p = 33 ∨ 1 + p = 61 ∨ 1 + p = 183 ∨ 1 + p = 671 ∨ 1 + p = 2013 := by
    have h5 : 1 + p ≤ 2013 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4)
  · have hp1 : p = 2 := by linarith
    have h5 : 3 * (1 + q) = 2013 := by linarith
    have h6 : 1 + q = 671 := by linarith
    have hq1 : q = 670 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 10 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 32 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 60 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 182 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 670 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 2012 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction


lemma round3_h2014_9ccd0328 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2014) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2014 := by
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := dvd_mul_right _ _
    rw [h] at h5; exact h5
  have h4 : 1 + p = 19 ∨ 1 + p = 38 ∨ 1 + p = 53 ∨ 1 + p = 106 ∨ 1 + p = 1007 ∨ 1 + p = 2014 := by
    have h5 : 1 + p ≤ 2014 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4)
  · have hp1 : p = 18 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 37 := by linarith
    have h5 : 38 * (1 + q) = 2014 := by linarith
    have h6 : 1 + q = 53 := by linarith
    have hq1 : q = 52 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 52 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 105 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 1006 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 2013 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction


lemma round3_h2019_9ccd0760 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h : (1 + p) * (1 + q) = 2019) : False := by
  have h1 : 1 + p ≥ 3 := by linarith [hp.two_le]
  have h2 : 1 + q ≥ 3 := by linarith [hq.two_le]
  have h3 : (1 + p) ∣ 2019 := by
    have h5 : (1 + p) ∣ (1 + p) * (1 + q) := dvd_mul_right _ _
    rw [h] at h5; exact h5
  have h4 : 1 + p = 3 ∨ 1 + p = 673 ∨ 1 + p = 2019 := by
    have h5 : 1 + p ≤ 2019 := by nlinarith
    interval_cases (1 + p) <;> norm_num at h3 ⊢ <;> omega
  rcases h4 with (h4 | h4 | h4)
  · have hp1 : p = 2 := by linarith
    have h5 : 3 * (1 + q) = 2019 := by linarith
    have h6 : 1 + q = 673 := by linarith
    have hq1 : q = 672 := by linarith
    rw [hq1] at hq; norm_num at hq <;> contradiction
  · have hp1 : p = 672 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction
  · have hp1 : p = 2018 := by linarith; rw [hp1] at hp; norm_num at hp <;> contradiction


lemma round2_sum_divisors_pq_case_is_2016 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (h_sum_range : 2010 ≤ (1 + p) * (1 + q) ∧ (1 + p) * (1 + q) ≤ 2019) :
    (1 + p) * (1 + q) = 2016 := by
  have h1 : (1 + p) * (1 + q) ≥ 2010 := h_sum_range.1
  have h2 : (1 + p) * (1 + q) ≤ 2019 := h_sum_range.2
  have h3 : (1 + p) * (1 + q) = 2010 ∨ (1 + p) * (1 + q) = 2011 ∨ (1 + p) * (1 + q) = 2012 ∨ (1 + p) * (1 + q) = 2013 ∨ (1 + p) * (1 + q) = 2014 ∨ (1 + p) * (1 + q) = 2015 ∨ (1 + p) * (1 + q) = 2016 ∨ (1 + p) * (1 + q) = 2017 ∨ (1 + p) * (1 + q) = 2018 ∨ (1 + p) * (1 + q) = 2019 := by omega
  rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3)
  · exact False.elim (round3_h2010_9cccf5f4 p q hp hq hne h3)
  · exact False.elim (round3_h2011_9ccce46a p q hp hq hne h3)
  · exact False.elim (round3_h2012_9cccfa36 p q hp hq hne h3)
  · exact False.elim (round3_h2013_9cccfe6e p q hp hq hne h3)
  · exact False.elim (round3_h2014_9ccd0328 p q hp hq hne h3)
  · exact False.elim (round3_h2015_9ccce8d4 p q hp hq hne h3)
  · exact h3
  · exact False.elim (round3_h2017_9ccced02 p q hp hq hne h3)
  · exact False.elim (round3_h2018_9cccf144 p q hp hq hne h3)
  · exact False.elim (round3_h2019_9ccd0760 p q hp hq hne h3)


lemma round1_h5_c091aa70 (m : ℕ)
  (hm : 1 < m)
  (h2 : ¬(∃ p k : ℕ, Nat.Prime p ∧ k > 0 ∧ m = p ^ k))
  (p : ℕ)
  (hp : Nat.Prime p)
  (hpdvd : p ∣ m):
  ∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧ q ≠ p := by
  by_contra h6
  push_neg at h6
  have h6' : ∀ (q : ℕ), Nat.Prime q → q ∣ m → q = p := by
    intro q hq_prime hq_dvd_m
    exact h6 q hq_prime hq_dvd_m
  have h5 : ∀ (n : ℕ), n > 0 → (∀ (q : ℕ), Nat.Prime q → q ∣ n → q = p) → (∃ k : ℕ, n = p ^ k) := by
    intro n hn_pos h
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h6 : n = 1
      · rw [h6]
        refine ⟨0, by simp⟩
      · have h7 : n > 1 := by omega
        have h8 : ∃ q : ℕ, Nat.Prime q ∧ q ∣ n := Nat.exists_prime_and_dvd (by linarith)
        rcases h8 with ⟨q, hq_prime, hq_dvd_n⟩
        have h9 : q = p := h q hq_prime hq_dvd_n
        have h10 : p ∣ n := by rw [h9] at hq_dvd_n; exact hq_dvd_n
        have h11 : ∃ t, n = p * t := exists_eq_mul_right_of_dvd h10
        rcases h11 with ⟨t, ht⟩
        have h12 : n = p * t := ht
        have h13 : t > 0 := by
          by_contra h13; have h13' : t = 0 := by linarith
          rw [h13'] at h12; linarith
        by_cases h14 : t = 1
        · have h15 : n = p := by rw [h12, h14]; <;> ring
          exact ⟨1, by rw [h15]; <;> ring⟩
        · have h14' : t > 1 := by omega
          have h17 : t < n := by
            have h172 : p ≥ 2 := Nat.Prime.two_le hp
            nlinarith
          have h18 : ∀ (r : ℕ), Nat.Prime r → r ∣ t → r = p := by
            intro r hr_prime hr_dvd_t
            have h19 : r ∣ n := by rw [h12]; exact dvd_mul_of_dvd_right hr_dvd_t p
            exact h r hr_prime h19
          have h20 : ∃ k : ℕ, t = p ^ k := ih t h17 h13 h18
          rcases h20 with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          rw [h12, hk]
          simp [pow_succ, mul_comm]
  have h21 : ∃ k : ℕ, m = p ^ k := h5 m (by linarith) h6'
  rcases h21 with ⟨k, hk⟩
  have h23 : k > 0 := by
    by_contra h23; have h23' : k = 0 := by linarith
    rw [h23'] at hk; have h24 : m = 1 := by simpa using hk; linarith
  have h25 : ∃ p k : ℕ, Nat.Prime p ∧ k > 0 ∧ m = p ^ k := ⟨p, k, hp, h23, hk⟩
  contradiction


lemma round1_h_final_c091ac78 (m : ℕ)
  (hm : 1 < m)
  (h_card : (Nat.divisors m).card = 4)
  (p : ℕ)
  (hp : Nat.Prime p)
  (hpdvd : p ∣ m)
  (q : ℕ)
  (hq_prime : Nat.Prime q)
  (hq_dvd_m : q ∣ m)
  (h_p_ne_q : p ≠ q):
  m = p * q := by
  have h1 : p * q ∣ m := by
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_primes hp hq_prime |>.mpr (by tauto)) hpdvd hq_dvd_m
  have h30 : 1 ∈ Nat.divisors m := Nat.mem_divisors.mpr ⟨one_dvd m, by linarith⟩
  have h31 : p ∈ Nat.divisors m := Nat.mem_divisors.mpr ⟨hpdvd, by linarith⟩
  have h32 : q ∈ Nat.divisors m := Nat.mem_divisors.mpr ⟨hq_dvd_m, by linarith⟩
  have h33 : p * q ∈ Nat.divisors m := Nat.mem_divisors.mpr ⟨h1, by nlinarith [Nat.Prime.two_le hp, Nat.Prime.two_le hq_prime]⟩
  have h34 : p > 1 := Nat.Prime.one_lt hp
  have h35 : q > 1 := Nat.Prime.one_lt hq_prime
  have h39 : 1 ≠ p := by linarith
  have h40 : 1 ≠ q := by linarith
  have h41 : 1 ≠ p * q := by nlinarith
  have h43 : p ≠ p * q := by nlinarith
  have h44 : q ≠ p * q := by nlinarith
  have h45 : ({1, p, q, p * q} : Finset ℕ) ⊆ Nat.divisors m := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact h30
    · exact h31
    · exact h32
    · exact h33
  have h46 : ({1, p, q, p * q} : Finset ℕ).card = 4 := by
    simp [h39, h40, h41, h_p_ne_q, h43, h44]
    <;> aesop
  have h49 : Nat.divisors m = ({1, p, q, p * q} : Finset ℕ) := by
    exact (Finset.eq_of_subset_of_card_le h45 (by linarith [h46, h_card])).symm
  have h51 : m ∈ Nat.divisors m := Nat.mem_divisors.mpr ⟨dvd_refl m, by linarith⟩
  rw [h49] at h51
  simp only [Finset.mem_insert, Finset.mem_singleton] at h51
  have h52 : m = 1 ∨ m = p ∨ m = q ∨ m = p * q := by tauto
  rcases h52 with (h52 | h52 | h52 | h52)
  · linarith
  · rw [h52] at hq_dvd_m
    have h54 : q ∣ p := hq_dvd_m
    have h55 : q = p := by
      have h551 := Nat.Prime.eq_one_or_self_of_dvd hp q h54
      have h5512 : q ≠ 1 := Nat.Prime.ne_one hq_prime
      omega
    tauto
  · rw [h52] at hpdvd
    have h54 : p ∣ q := hpdvd
    have h55 : p = q := by
      have h551 := Nat.Prime.eq_one_or_self_of_dvd hq_prime p h54
      have h5512 : p ≠ 1 := Nat.Prime.ne_one hp
      omega
    tauto
  · exact h52


lemma round2_card_divisors_eq_four_form (m : ℕ) (hm : 1 < m) (h_card : (Nat.divisors m).card = 4) :
  (∃ p, Nat.Prime p ∧ m = p ^ 3) ∨ (∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ m = p * q) := by
  by_cases h : ∃ p k : ℕ, Nat.Prime p ∧ k > 0 ∧ m = p ^ k
  · rcases h with ⟨p, k, hp, hk_pos, h_eq⟩
    have h1 : (Nat.divisors (p ^ k)).card = k + 1 := by
      rw [Nat.divisors_prime_pow hp]
      simp [Finset.card_range]
    have h3 : (Nat.divisors (p ^ k)).card = 4 := by rw [h_eq] at h_card; exact h_card
    have h4 : k + 1 = 4 := by linarith
    have hk : k = 3 := by omega
    left
    refine ⟨p, hp,?_⟩
    rw [h_eq, hk]; <;> norm_num
  · have h3 : ∃ p : ℕ, Nat.Prime p ∧ p ∣ m := Nat.exists_prime_and_dvd (by linarith)
    rcases h3 with ⟨p, hp, hpdvd⟩
    have h4 : ∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧ q ≠ p := round1_h5_c091aa70 m hm h p hp hpdvd
    rcases h4 with ⟨q, hq_prime, hq_dvd_m, hq_ne_p⟩
    have h53 : m = p * q := round1_h_final_c091ac78 m hm h_card p hp hpdvd q hq_prime hq_dvd_m (by tauto)
    right
    refine ⟨p, q, hp, hq_prime, by tauto, h53⟩


lemma round3_card_divisors_eq_four_imp_one_lt_m (m : ℕ) (h_card : (Nat.divisors m).card = 4) : 1 < m := by
  by_contra h
  have h₁ : m ≤ 1 := by linarith
  interval_cases m <;> simp (config := {decide := true}) [Nat.divisors] at h_card <;> contradiction


lemma round3_sum_divisors_of_prod_of_distinct_primes (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    (∑ i in Nat.divisors (p * q), i) = (1 + p) * (1 + q) := by
  have h_divs := round4_divisors_of_pq_7d12b6ea p q hp hq hne
  have h_sum : (∑ d in Nat.divisors (p * q), d) = 1 + p + q + p * q := h_divs.2
  rw [h_sum]
  ring


lemma round4_k_in_S_implies_k_eq_2016 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) :
    ∀ k, k ∈ S → k = 2016 := by
  intro k hk
  have h₁ : 2010 ≤ k ∧ k ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = k := by
    exact (h₀ k).mp hk
  rcases h₁ with ⟨hk_range_left, hk_range_right, m, hm_card, hm_sum⟩
  have hm1 : 1 < m := round3_card_divisors_eq_four_imp_one_lt_m m hm_card
  have h_m_form : (∃ p, Nat.Prime p ∧ m = p ^ 3) ∨ (∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ m = p * q) :=
    round2_card_divisors_eq_four_form m hm1 hm_card
  cases h_m_form with
  | inl h_m_form_p_cubed =>
    rcases h_m_form_p_cubed with ⟨p, hp, hm_eq_p_cubed⟩
    have h_sum_p_cubed : (∑ p in Nat.divisors m, p) = (∑ p in Nat.divisors (p ^ 3), p) := by
      rw [hm_eq_p_cubed]
    have hk_sum_p_cubed : k = (∑ p in Nat.divisors (p ^ 3), p) := by linarith
    have h_sum_p_cubed_range : 2010 ≤ (∑ p in Nat.divisors (p ^ 3), p) ∧ (∑ p in Nat.divisors (p ^ 3), p) ≤ 2019 := by
      constructor <;> linarith
    exact False.elim (round2_sum_divisors_p_cubed_case_empty p hp h_sum_p_cubed_range)
  | inr h_m_form_pq =>
    rcases h_m_form_pq with ⟨p, q, hp, hq, hne, hm_eq_pq⟩
    have h_sum_pq : (∑ p in Nat.divisors m, p) = (∑ p in Nat.divisors (p * q), p) := by
      rw [hm_eq_pq]
    have hk_sum_pq : k = (∑ p in Nat.divisors (p * q), p) := by linarith
    have h_sum_pq_formula : (∑ p in Nat.divisors (p * q), p) = (1 + p) * (1 + q) :=
      round3_sum_divisors_of_prod_of_distinct_primes p q hp hq hne
    have hk_eq_prod : k = (1 + p) * (1 + q) := by linarith
    have h_prod_range : 2010 ≤ (1 + p) * (1 + q) ∧ (1 + p) * (1 + q) ≤ 2019 := by
      constructor <;> linarith
    have h_prod_eq_2016 : (1 + p) * (1 + q) = 2016 := by
      exact round2_sum_divisors_pq_case_is_2016 p q hp hq hne h_prod_range
    linarith


theorem mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) :
    (∑ k in S, k) = 2016 := by
  have h_S_subset_2016 : ∀ k, k ∈ S → k = 2016 := round4_k_in_S_implies_k_eq_2016 S h₀

  have h_2016_in_S : 2016 ∈ S := round1_2016_in_S S h₀

  have h_S_eq_singleton_2016 : S = ({2016} : Finset ℕ) := by
    apply Finset.Subset.antisymm
    · intro k hk
      have hk_eq_2016 : k = 2016 := h_S_subset_2016 k hk
      rw [hk_eq_2016]
      <;> simp
    · intro k hk
      simp only [Finset.mem_singleton] at hk
      rw [hk]
      exact h_2016_in_S

  rw [h_S_eq_singleton_2016]
  <;> norm_num
