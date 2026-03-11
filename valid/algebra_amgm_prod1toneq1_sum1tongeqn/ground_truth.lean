import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 800000

theorem algebra_amgm_prod1toneq1_sum1tongeqn (a : ℕ → NNReal) (n : ℕ)
  (h₀ : Finset.prod (Finset.range n) a = 1) : Finset.sum (Finset.range n) a ≥ n := by
  rcases n with _ | n
  · simp
  · set N : NNReal := ((n + 1 : ℕ) : NNReal) with hN_def
    have hN_ne : N ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hw : ∑ _i ∈ Finset.range (n + 1), N⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hN_ne]
    have amgm := NNReal.geom_mean_le_arith_mean_weighted
      (Finset.range (n + 1)) (fun _ => N⁻¹) a hw
    rw [NNReal.finset_prod_rpow, h₀, NNReal.one_rpow] at amgm
    rw [← Finset.mul_sum] at amgm
    show N ≤ _
    have h1 : N * 1 ≤ N * (N⁻¹ * ∑ i ∈ Finset.range (n + 1), a i) :=
      mul_le_mul_of_nonneg_left amgm (zero_le N)
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul] at h1
    exact h1
