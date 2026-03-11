import Mathlib

open BigOperators Real Nat Topology Rat

private def allCands : Finset ℕ :=
  (Finset.range 9 ×ˢ (Finset.range 5 ×ˢ (Finset.range 4 ×ˢ Finset.range 2))).image
    (fun t : ℕ × ℕ × ℕ × ℕ => 2 ^ t.1 * 3 ^ t.2.1 * 5 ^ t.2.2.1 * 7 ^ t.2.2.2)

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
private lemma allCands_eq_divisors : allCands = Nat.divisors 18144000 := by
  unfold allCands
  have h1 : (18144000 : ℕ) = 2 ^ 8 * (3 ^ 4 * (5 ^ 3 * 7)) := by norm_num
  rw [h1, Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul]
  rw [Nat.divisors_prime_pow (by decide : Nat.Prime 2),
      Nat.divisors_prime_pow (by decide : Nat.Prime 3),
      Nat.divisors_prime_pow (by decide : Nat.Prime 5),
      Nat.Prime.divisors (by decide : Nat.Prime 7)]
  decide

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private lemma filter_card :
    (allCands.filter (fun n => 5 ∣ n ∧ Nat.lcm 120 n = 5 * Nat.gcd 3628800 n)).card = 48 := by
  unfold allCands
  decide

set_option maxHeartbeats 400000 in
theorem amc12a_2020_p21 (S : Finset ℕ)
  (h₀ : ∀ n : ℕ, n ∈ S ↔ 5 ∣ n ∧ Nat.lcm 5! n = 5 * Nat.gcd 10! n) : S.card = 48 := by
  have hS : S = allCands.filter
      (fun n => 5 ∣ n ∧ Nat.lcm 120 n = 5 * Nat.gcd 3628800 n) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · intro hn
      have hmem := (h₀ n).mp hn
      obtain ⟨h5, hlcm⟩ := hmem
      refine ⟨?_, h5, ?_⟩
      · -- n ∈ allCands
        rw [allCands_eq_divisors, Nat.mem_divisors]
        refine ⟨?_, by norm_num⟩
        have h1 : n ∣ Nat.lcm (Nat.factorial 5) n := Nat.dvd_lcm_right _ _
        rw [hlcm] at h1
        exact dvd_trans h1 (Nat.mul_dvd_mul_left 5 (Nat.gcd_dvd_left _ _) |>.trans (by norm_num))
      · -- lcm 120 n = 5 * gcd 3628800 n
        have : Nat.factorial 5 = 120 := by norm_num
        have : Nat.factorial 10 = 3628800 := by norm_num
        rwa [‹Nat.factorial 5 = 120›, ‹Nat.factorial 10 = 3628800›] at hlcm
    · intro ⟨_, h5, hlcm⟩
      rw [h₀]
      refine ⟨h5, ?_⟩
      have : Nat.factorial 5 = 120 := by norm_num
      have : Nat.factorial 10 = 3628800 := by norm_num
      rwa [‹Nat.factorial 5 = 120›, ‹Nat.factorial 10 = 3628800›]
  rw [hS]
  exact filter_card
