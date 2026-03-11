import Mathlib
import Aesop

set_option maxHeartbeats 3200000

open BigOperators Real Nat Topology Rat

-- Auxiliary definitions and lemmas for the proof of imo_1974_p3.
-- We work in F_25 = F_5[alpha]/(alpha^2 - 3) represented as pairs in ZMod 5.
-- The pair recurrence PQ tracks (1+alpha)^m = P(m) + Q(m)*alpha.
-- The original sum mod 5 equals Q(2n+1), which is always nonzero (period 24).

section imo_1974_p3_aux

open Finset

private def BP (m N : ℕ) : ZMod 5 :=
  ∑ k ∈ range N, (Nat.choose m (2 * k) : ZMod 5) * 3 ^ k

private def BS (m N : ℕ) : ZMod 5 :=
  ∑ k ∈ range N, (Nat.choose m (2 * k + 1) : ZMod 5) * 3 ^ k

private lemma pascal_odd (m k : ℕ) :
    (Nat.choose (m + 1) (2 * k + 1) : ZMod 5) =
    (Nat.choose m (2 * k) : ZMod 5) + (Nat.choose m (2 * k + 1) : ZMod 5) := by
  have h := Nat.choose_succ_succ m (2 * k); push_cast [h]; ring

private lemma pascal_even (m k : ℕ) :
    (Nat.choose (m + 1) (2 * (k + 1)) : ZMod 5) =
    (Nat.choose m (2 * k + 1) : ZMod 5) + (Nat.choose m (2 * (k + 1)) : ZMod 5) := by
  have h := Nat.choose_succ_succ m (2 * k + 1)
  have heq : (2 * k + 1).succ = 2 * (k + 1) := by omega
  rw [heq] at h; push_cast [h]; ring

private lemma BS_succ (m N : ℕ) : BS (m + 1) N = BP m N + BS m N := by
  simp only [BS, BP, ← Finset.sum_add_distrib]
  congr 1; ext k; rw [← add_mul]; congr 1; exact pascal_odd m k

private lemma BP_succ (m N : ℕ) : BP (m + 1) (N + 1) = BP m (N + 1) + 3 * BS m N := by
  have lhs_eq : BP (m + 1) (N + 1) =
      1 + ∑ k ∈ range N, (Nat.choose (m + 1) (2 * (k + 1)) : ZMod 5) * 3 ^ (k + 1) := by
    simp only [BP]
    rw [Finset.sum_range_succ' (f := fun k => (Nat.choose (m+1) (2*k) : ZMod 5) * 3^k)]
    simp [Nat.choose_zero_right, add_comm]
  have rhs_eq : BP m (N + 1) + 3 * BS m N =
      1 + ∑ k ∈ range N, (Nat.choose m (2 * (k + 1)) : ZMod 5) * 3 ^ (k + 1) +
      3 * BS m N := by
    simp only [BP]
    rw [Finset.sum_range_succ' (f := fun k => (Nat.choose m (2*k) : ZMod 5) * 3^k)]
    simp [Nat.choose_zero_right, add_comm]
  rw [lhs_eq, rhs_eq, add_assoc, add_left_cancel_iff]
  rw [show 3 * BS m N = ∑ k ∈ range N, (Nat.choose m (2*k+1) : ZMod 5) * 3^(k+1) from by
    simp only [BS, Finset.mul_sum]; congr 1; ext k; ring]
  rw [← Finset.sum_add_distrib]
  congr 1; ext i; rw [pascal_even m i]; ring

private lemma BP_zero (N : ℕ) (hN : 0 < N) : BP 0 N = 1 := by
  simp only [BP]; rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; simp [Nat.choose_eq_zero_of_lt (by omega : 0 < 2 * k)]
  · intro h; exact absurd (Finset.mem_range.mpr hN) h

private lemma BS_zero (N : ℕ) : BS 0 N = 0 := by
  simp only [BS]; apply Finset.sum_eq_zero
  intro k _; simp [Nat.choose_eq_zero_of_lt (by omega : 0 < 2 * k + 1)]

private def PQ : ℕ → ZMod 5 × ZMod 5
  | 0 => (1, 0)
  | n + 1 => let (p, q) := PQ n; (p + 3 * q, p + q)

private lemma BP_extend' (m : ℕ) : BP m (m + 2) = BP m (m + 1) := by
  simp only [BP, Finset.sum_range_succ]
  simp [Nat.choose_eq_zero_of_lt (show m < 2 * (m + 1) by omega)]

private lemma BS_extend' (m : ℕ) : BS m (m + 2) = BS m (m + 1) := by
  simp only [BS, Finset.sum_range_succ]
  simp [Nat.choose_eq_zero_of_lt (show m < 2 * (m + 1) + 1 by omega)]

private lemma BPBS_eq_PQ (m : ℕ) : BP m (m + 1) = (PQ m).1 ∧ BS m (m + 1) = (PQ m).2 := by
  induction m with
  | zero => exact ⟨BP_zero 1 (by omega), BS_zero 1⟩
  | succ m ih =>
    obtain ⟨ihP, ihS⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [show m + 1 + 1 = (m + 1) + 1 from rfl, BP_succ m (m + 1), BP_extend', ihP, ihS]
      simp [PQ]
    · rw [show m + 1 + 1 = m + 2 from rfl, BS_succ m (m + 2), BP_extend', BS_extend', ihP, ihS]
      simp [PQ]

private lemma BS_truncate (n : ℕ) : BS (2*n+1) (2*n+2) = BS (2*n+1) (n+1) := by
  simp only [BS]; symm
  apply Finset.sum_subset
  · intro k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intro k hk1 hk2
    rw [Finset.mem_range] at hk1 hk2; push_neg at hk2
    simp [Nat.choose_eq_zero_of_lt (show 2*n+1 < 2*k+1 by omega)]

private def Q' (n : ℕ) : ZMod 5 := (PQ n).2

private lemma Q'_eq_sum (n : ℕ) :
    Q' (2*n+1) = ∑ k ∈ range (n + 1), (Nat.choose (2*n+1) (2*k+1) : ZMod 5) * 3 ^ k := by
  rw [Q', ← (BPBS_eq_PQ (2*n+1)).2, BS_truncate, BS]

private lemma PQ_congr (a b : ℕ) (h : PQ a = PQ b) : PQ (a + 1) = PQ (b + 1) := by
  simp only [PQ, h]

private lemma PQ_period_24 (m : ℕ) : PQ (m + 24) = PQ m := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 + 24 = (n + 24) + 1 from by ring]
    exact PQ_congr (n + 24) n ih

private lemma Q'_period_24 (m : ℕ) : Q' (m + 24) = Q' m := by
  simp only [Q', PQ_period_24]

private lemma Q'_odd_nonzero_base : ∀ i : Fin 12, Q' (2 * i.val + 1) ≠ 0 := by decide

private lemma Q'_odd_ne_zero (n : ℕ) : Q' (2 * n + 1) ≠ 0 := by
  have hmod : Q' (2 * n + 1) = Q' (2 * (n % 12) + 1) := by
    conv_lhs => rw [show n = 12 * (n / 12) + n % 12 from (Nat.div_add_mod n 12).symm]
    generalize n / 12 = q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show 2 * (12 * (q + 1) + n % 12) + 1 = (2 * (12 * q + n % 12) + 1) + 24 from by ring]
      rw [Q'_period_24, ih]
  rw [hmod]
  exact Q'_odd_nonzero_base ⟨n % 12, Nat.mod_lt n (by norm_num)⟩

end imo_1974_p3_aux

theorem imo_1974_p3
  (n : ℕ) :
  ¬ 5∣∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by
  simp_rw [show ∀ k, 2 ^ (3 * k) = 8 ^ k from fun k => by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num, ← pow_mul, mul_comm]]
  intro hdvd
  have h0 : (↑(∑ k ∈ Finset.range (n+1), Nat.choose (2*n+1) (2*k+1) * 8^k) : ZMod 5) = 0 := by
    rwa [ZMod.natCast_eq_zero_iff]
  push_cast at h0
  simp_rw [show (8 : ZMod 5) = 3 from by decide] at h0
  rw [← Q'_eq_sum] at h0
  exact Q'_odd_ne_zero n h0
