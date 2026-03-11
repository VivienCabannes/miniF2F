import Mathlib
import Aesop

set_option maxHeartbeats 3200000

open BigOperators Real Nat Topology Rat

-- d(p^k) = k+1 for prime p
lemma card_divisors_prime_pow' {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    (Nat.divisors (p ^ k)).card = k + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

-- The core identity: d(p*n) * (v+1) = d(n) * (v+2) where v = v_p(n)
lemma divisors_mul_prime_identity (n : ℕ) (hn : n ≠ 0) (p : ℕ) (hp : Nat.Prime p) :
    (Nat.divisors (p * n)).card * (n.factorization p + 1) =
    (Nat.divisors n).card * (n.factorization p + 2) := by
  set v := n.factorization p
  -- m = n / p^v (the p-free part of n)
  set m := n / p ^ v with hm_def
  have hm_cop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn
  have hn_eq : p ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hpn_eq : p * n = p ^ (v + 1) * m := by
    rw [← hn_eq, pow_succ]; ring
  have hdn : (Nat.divisors n).card = (v + 1) * (Nat.divisors m).card := by
    conv_lhs => rw [← hn_eq]
    rw [(hm_cop.pow_left v).card_divisors_mul, card_divisors_prime_pow' hp]
  have hdpn : (Nat.divisors (p * n)).card = (v + 2) * (Nat.divisors m).card := by
    rw [hpn_eq, (hm_cop.pow_left (v + 1)).card_divisors_mul, card_divisors_prime_pow' hp]
  rw [hdpn, hdn]; ring

theorem mathd_numbertheory_709 (n : ℕ) (h₀ : 0 < n) (h₁ : Finset.card (Nat.divisors (2 * n)) = 28)
  (h₂ : Finset.card (Nat.divisors (3 * n)) = 30) : Finset.card (Nat.divisors (6 * n)) = 35 := by
  have hn : n ≠ 0 := Nat.pos_iff_ne_zero.mp h₀
  set D := (Nat.divisors n).card
  set D6 := (Nat.divisors (6 * n)).card
  have h840 : D6 * D = 840 := by
    have h_gcd : Nat.gcd (2 * n) (3 * n) = n := by
      rw [show 2 * n = n * 2 from by ring, show 3 * n = n * 3 from by ring, Nat.gcd_mul_left]
      norm_num
    have h_lcm : Nat.lcm (2 * n) (3 * n) = 6 * n := by
      rw [show 2 * n = n * 2 from by ring, show 3 * n = n * 3 from by ring, Nat.lcm_mul_left]
      norm_num; ring
    have hσ := ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply
      (ArithmeticFunction.isMultiplicative_sigma (k := 0)) (x := 2 * n) (y := 3 * n)
    simp only [ArithmeticFunction.sigma_zero_apply] at hσ
    rw [h_gcd, h_lcm] at hσ; nlinarith
  have hD_pos : 0 < D :=
    Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩⟩
  have hD6_pos : 0 < D6 :=
    Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩⟩
  set v₂ := n.factorization 2
  set v₃ := n.factorization 3
  have h_id2 : 28 * (v₂ + 1) = D * (v₂ + 2) := by
    have := divisors_mul_prime_identity n hn 2 (by norm_num)
    rw [h₁] at this; linarith
  have h_id3 : 30 * (v₃ + 1) = D * (v₃ + 2) := by
    have := divisors_mul_prime_identity n hn 3 (by norm_num)
    rw [h₂] at this; linarith
  have h6_v2 : D6 * (v₂ + 1) = 30 * (v₂ + 2) :=
    Nat.eq_of_mul_eq_mul_right (show 0 < 28 by omega)
      (show D6 * (v₂ + 1) * 28 = 30 * (v₂ + 2) * 28 by nlinarith)
  have h6_v3 : D6 * (v₃ + 1) = 28 * (v₃ + 2) :=
    Nat.eq_of_mul_eq_mul_right (show 0 < 30 by omega)
      (show D6 * (v₃ + 1) * 30 = 28 * (v₃ + 2) * 30 by nlinarith)
  have hv2_dvd : (v₂ + 1) ∣ 30 := by
    have h1 : (v₂ + 1) ∣ (v₂ + 1) * D6 := dvd_mul_right _ _
    rw [show (v₂ + 1) * D6 = D6 * (v₂ + 1) from by ring, h6_v2,
        show 30 * (v₂ + 2) = 30 * (v₂ + 1) + 30 from by ring] at h1
    exact (Nat.dvd_add_right (dvd_mul_left _ _)).mp h1
  have hv3_dvd : (v₃ + 1) ∣ 28 := by
    have h1 : (v₃ + 1) ∣ (v₃ + 1) * D6 := dvd_mul_right _ _
    rw [show (v₃ + 1) * D6 = D6 * (v₃ + 1) from by ring, h6_v3,
        show 28 * (v₃ + 2) = 28 * (v₃ + 1) + 28 from by ring] at h1
    exact (Nat.dvd_add_right (dvd_mul_left _ _)).mp h1
  have hD6_dvd : D6 ∣ 840 := ⟨D, h840.symm⟩
  have hD6_ge : 31 ≤ D6 := by
    have hv2_le : v₂ + 1 ≤ 30 := Nat.le_of_dvd (by omega) hv2_dvd
    nlinarith
  obtain ⟨a, ha⟩ := hv2_dvd
  have ha_pos : 0 < a := Nat.pos_of_mul_pos_left (show 0 < (v₂ + 1) * a by omega)
  have hD6_eq_a : D6 = 30 + a := by
    have : D6 * (v₂ + 1) = (30 + a) * (v₂ + 1) := by nlinarith
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < v₂ + 1) this
  obtain ⟨b, hb⟩ := hv3_dvd
  have hb_pos : 0 < b := Nat.pos_of_mul_pos_left (show 0 < (v₃ + 1) * b by omega)
  have hD6_eq_b : D6 = 28 + b := by
    have : D6 * (v₃ + 1) = (28 + b) * (v₃ + 1) := by nlinarith
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < v₃ + 1) this
  have hab : b = a + 2 := by omega
  have ha_dvd : a ∣ 30 := ⟨v₂ + 1, by linarith⟩
  have hab_dvd : (a + 2) ∣ 28 := by rw [← hab]; exact ⟨v₃ + 1, by linarith⟩
  have hda_dvd : (30 + a) ∣ 840 := by rw [← hD6_eq_a]; exact hD6_dvd
  have ha_le : a ≤ 30 := Nat.le_of_dvd (by omega) ha_dvd
  rw [hD6_eq_a]; interval_cases a <;> omega
