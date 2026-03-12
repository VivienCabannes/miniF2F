import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 1600000

namespace Imo1987P6

open Nat

lemma minFac_le_sq {n : ℕ} (hnezero : n ≠ 0) (hn : minFac n ≠ n) :
    (minFac n)^2 ≤ n := by
  match n with
  | 0 => contradiction
  | 1 => simp
  | n+2 =>
    obtain ⟨r,hr⟩ := Nat.minFac_dvd (n+2)
    match r with
    | 0 => omega
    | 1 => nth_rw 2 [hr] at hn; simp at hn
    | r+2 =>
      have hh : (r+2) ∣ (n+2) := ⟨minFac (n+2), (by nth_rw 1 [hr,mul_comm])⟩
      have hr' : minFac (n+2) ≤ (r+2) := Nat.minFac_le_of_dvd (by omega) hh
      calc
      _ = (minFac (n+2)) * minFac (n+2) := by ring_nf
      _ ≤ minFac (n+2) * (r+2) := Nat.mul_le_mul_left _ hr'
      _ = _ := hr.symm

lemma prime_of_coprime' (n : ℕ) (h1 : 1 < n)
    (h2 : ∀ m:ℕ, m^2 ≤ n → m ≠ 0 → n.Coprime m) : Nat.Prime n := by
  rw [Nat.prime_def_minFac]
  by_contra H; push_neg at H
  replace H := H (by omega)
  have nneone : n ≠ 1 := by omega
  have _mpos := Nat.minFac_pos n
  have h2' := h2 (minFac n) (minFac_le_sq (by omega) H) (by omega)
  exact absurd h2' (Nat.Prime.not_coprime_iff_dvd.2
    ⟨minFac n, Nat.minFac_prime nneone, Nat.minFac_dvd n, dvd_refl (minFac n)⟩)

lemma dyadic {k b : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ b) :
    ∃ i, b < 2^i * k ∧ 2^i * k ≤ 2 * b := by
  have hbk : b/k ≠ 0 := by
    apply (Nat.div_ne_zero_iff (a:=b) (b:=k)).2
    omega
  use Nat.log2 (b/k) + 1
  constructor
  · have h2bk: (b/k).log2 < (b/k).log2 + 1 := Nat.lt_succ_self _
    replace h2bk := (Nat.log2_lt hbk).1 h2bk
    replace h2bk := succ_le_of_lt h2bk
    calc
    _ < b/k * k + k := lt_div_mul_add (by omega)
    _ = (b/k+1) *k := by ring
    _ ≤ 2 ^((b/k).log2 +1) * k := Nat.mul_le_mul_right k h2bk
  · have h2' : 2 ^((b/k).log2 +1) = 2 * 2^( (b/k).log2 ) :=
      by rw [pow_succ _ _, mul_comm]
    rw [h2']
    have h3 : 2^((b/k).log2) ≤ b/k := Nat.log2_self_le hbk
    rw [mul_assoc]
    apply Nat.mul_le_mul_left 2
    exact (Nat.le_div_iff_mul_le h1).mp h3

lemma key_lemma {m b: ℕ}
    (h: ∀ k, b < k → k ≤ 2*b → Coprime m k) :
     ∀ k, 1 < k → k ≤ 2 * b → Coprime m k := by
   intro k hk1 hk2
   by_cases hk0 : b < k
   · exact h k hk0 hk2
   · push_neg at hk0
     obtain ⟨i, hi1, hi2⟩ := dyadic (le_of_lt hk1) hk0
     exact Coprime.coprime_mul_left_right (h (2 ^ i * k) hi1 hi2)

lemma key_lemma' {m b: ℕ} (h1 : 1 < m)
    (h: ∀ k, b < k → k ≤ 2*b → Coprime m k) (h2 : m < (2*b+1)^2) :
     Nat.Prime m := by
  replace h := key_lemma h
  apply prime_of_coprime' m h1
  intro k hk1 hk2
  by_cases hk0 : k = 1
  · simp [hk0]
  push_neg at hk0
  refine h k ?_ ?_
  · omega
  · replace h2 := lt_of_le_of_lt hk1 h2
    rw [pow_two, pow_two] at h2
    replace h2 := Nat.mul_self_lt_mul_self_iff.1 h2
    omega

lemma dvd_lemma (a b c : ℕ) (h : c ≠ 0) : a ≤ b → b ∣ c → c < 2 * a → b = c := by
  intro h1 ⟨k, hk⟩ h3
  match k with
  | 0 => simp at hk; exfalso; exact h hk
  | 1 => simp [hk]
  | k + 2 => nlinarith

lemma arith_identity (kk ss s r p j : ℕ)
    (hksr : kk = s + r) (hss0 : j = ss + (s + r + 1)) (hj2 : j ≤ 2 * kk) :
    kk ^ 2 + kk + p = ss ^ 2 + ss + p + (2 * kk - j + 1) * j := by
  zify [hj2]
  subst hksr
  rw [hss0]
  push_cast
  ring

end Imo1987P6

open Imo1987P6 in
theorem imo_1987_p6 (p : ℕ) (f : ℕ → ℕ) (h_def : ∀ x, f x = x ^ 2 + x + p)
  (h₀ : ∀ k : ℕ, k ≤ Nat.floor (Real.sqrt (p / 3)) → Nat.Prime (f k)) :
   ∀ i ≤ p - 2, Nat.Prime (f i) := by
  simp only [h_def] at h₀ ⊢
  let r := Nat.floor (Real.sqrt (↑p / 3))
  intro k
  apply Nat.case_strong_induction_on k
  · intro; exact h₀ 0 (Nat.zero_le _)
  intro k IH hk
  by_cases h : k + 1 ≤ r
  · exact h₀ (k + 1) h
  · push_neg at h
    set kk := k + 1 with hkk_def
    set s := kk - r with hs_def
    set N := kk ^ 2 + kk + p with hN_def
    have hksr : kk = s + r := Nat.eq_add_of_sub_eq (le_of_lt h) (by rfl)
    have hs : 1 ≤ s := by
      rw [hs_def, hkk_def]
      exact Nat.le_sub_of_add_le' h
    have ieq3 : 3 * r ≤ 6 * r * s := by nlinarith only [hs]
    have ieq4 : p ≤ 3 * r ^ 2 + 6 * r + 2 := by
      have ieq5 : √ (↑p / 3) < ↑r + 1 := Nat.lt_floor_add_one _
      replace ieq5 := Real.lt_sq_of_sqrt_lt ieq5 |> (div_lt_iff₀ (by norm_num : (0:ℝ) < 3)).1
      replace ieq5 : (p) < (3 * r ^ 2 + 6 * r + 3) := cast_lt.1 <| by
        have casteq : ((r : ℝ) + 1) ^ 2 * 3 = ((3 * r ^ 2 + 6 * r + 3 : ℕ) : ℝ) := by
          push_cast; ring
        rw [← casteq]
        exact ieq5
      omega
    have hN1 : N < (2 * (s + r) + 1) ^ 2 := by
      rw [hN_def]
      calc
      kk ^ 2 + kk + p
          ≤ 3 * r ^ 2 + 6 * r + 2 + (r + s) * (r + s + 1) := by
          nlinarith only [ieq4, hs, hksr]
      _ = 4 * r ^ 2 + 2 * r * s + s ^ 2 + 7 * r + s + 2 := by ring_nf
      _ < 4 * r ^ 2 + 4 * s ^ 2 + 8 * r * s + 4 * r + 4 * s + 1 := by nlinarith only [hs]
      _ = _ := by ring
    rw [← hksr] at hN1
    have hP : ∀ i, kk < i → i ≤ 2 * kk → Coprime N i := by
      by_contra H
      push_neg at H
      obtain ⟨j, hj1, hj2, hj3⟩ := H
      have hj1' : s + r + 1 ≤ j := by rw [← hksr]; exact succ_le_of_lt hj1
      set ss := j - (s + r + 1) with hss_def
      have hss0 : j = ss + (s + r + 1) := Nat.eq_add_of_sub_eq hj1' (by rfl)
      have hp : 2 ≤ p := by omega
      have hss1 : ss ≤ k := by
        apply Nat.le_of_add_le_add_right (b := s + r + 1)
        rw [← hss0, ← hksr]
        calc
        _ ≤ _ := hj2
        _ = _ := by omega
      replace hss1 : Nat.Prime (ss ^ 2 + ss + p) := IH ss hss1 (by omega)
      have hfss : N = (ss ^ 2 + ss + p) + (2 * kk - j + 1) * j := by
        rw [hN_def]
        exact arith_identity kk ss s r p j hksr hss0 hj2
      change ¬ Coprime N j at hj3
      rw [hfss, Nat.coprime_add_mul_right_left] at hj3
      have hss2 : (ss ^ 2 + ss + p) ∣ j := hss1.dvd_iff_not_coprime.2 hj3
      have hfss1 : p ≤ ss ^ 2 + ss + p := Nat.le_add_left p (ss ^ 2 + ss)
      have hfss2 : j < 2 * p := by omega
      have hj' : j ≠ 0 := by omega
      have hfss3 : ss ^ 2 + ss + p = j :=
        dvd_lemma _ _ _ hj' hfss1 hss2 hfss2
      rw [hss0, show ss + (s + r + 1) = ss + s + r + 1 from by omega] at hfss3
      have hfss4 : ss ^ 2 + p = s + r + 1 := by omega
      have hc1 : p ≤ k + 2 := by
        calc
          p ≤ ss ^ 2 + p := Nat.le_add_left _ _
          _ = s + r + 1 := hfss4
          _ = kk + 1 := by rw [← hksr]
          _ = k + 2 := by omega
      have hc2 : p ≤ p - 1 := by omega
      omega
    have hfk : 1 < N := by
      rw [hN_def, hksr]
      calc
      _ < 1 + 1 := by omega
      _ ≤ s ^ 2 + s := by nlinarith only [hs]
      _ ≤ s ^ 2 + 2 * r * s + r ^ 2 + s + r + p := by omega
      _ = (s + r) ^ 2 + (s + r) + p := by ring
    have hgoal : Nat.Prime N := key_lemma' hfk hP hN1
    rw [hN_def, hkk_def] at hgoal
    exact hgoal
