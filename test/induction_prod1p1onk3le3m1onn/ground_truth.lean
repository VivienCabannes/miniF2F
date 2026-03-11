import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_prod1p1onk3le3m1onn
  (n : ℕ)
  (h₀ : 0 < n) :
  ∏ k ∈ Finset.Icc 1 n, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / ↑n := by
  have h_main : ∀ (m : ℕ), 0 < m → (∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑m := by
    intro m hm
    have h₁ : ∀ (n : ℕ), 0 < n → (∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑n := by
      intro n hn
      induction' hn with n hn IH
      · norm_num [Finset.prod_Icc_succ_top]
      · rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n.succ)]
        refine' le_trans (mul_le_mul_of_nonneg_right IH (by positivity)) _
        cases n with
        | zero =>
          norm_num [Finset.prod_Icc_succ_top] at *
        | succ n =>
          field_simp [Nat.cast_add_one_ne_zero]
          ring_nf
          norm_num
          apply le_of_sub_nonneg
          field_simp
          ring_nf
          positivity
    exact h₁ m hm
  have h_final : (∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑n := by
    apply h_main n h₀
  exact h_final