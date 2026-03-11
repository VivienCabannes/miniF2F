import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_sumkexp3eqsumksq
  (n : ℕ) :
  ∑ k ∈ Finset.range n, k^3 = (∑ k ∈ Finset.range n, k)^2 := by
  have h_main : ∀ n : ℕ, (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
    intro n
    have h₁ : (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
      have h₂ : ∀ n : ℕ, (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
          have h₃ : ∑ k in Finset.range n, k = n * (n - 1) / 2 := by
            rw [Finset.sum_range_id]
          have h₄ : 2 ∣ n * (n - 1) := by
            have h₅ : n * (n - 1) % 2 = 0 := by
              have h₆ : n % 2 = 0 ∨ n % 2 = 1 := by omega
              rcases h₆ with (h₆ | h₆) <;> cases n with
              | zero => simp
              | succ n =>
                simp [h₆, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.succ_pos]
                <;> ring_nf at * <;> omega
            omega
          have h₅ : 2 * (∑ k in Finset.range n, k) = n * (n - 1) := by
            rw [h₃]
            have h₆ : 2 ∣ n * (n - 1) := h₄
            have h₇ : n * (n - 1) / 2 * 2 = n * (n - 1) := by
              have h₈ : n * (n - 1) % 2 = 0 := by omega
              have h₉ : n * (n - 1) / 2 * 2 = n * (n - 1) := by
                have h₁₀ : n * (n - 1) = 2 * (n * (n - 1) / 2) := by
                  omega
                omega
              exact h₉
            omega
          have h₆ : n ^ 3 = 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by
            have h₇ : 2 * n * (∑ k in Finset.range n, k) = n ^ 2 * (n - 1) := by
              have h₈ : 2 * (∑ k in Finset.range n, k) = n * (n - 1) := h₅
              have h₉ : 2 * n * (∑ k in Finset.range n, k) = n * (n * (n - 1)) := by
                calc
                  2 * n * (∑ k in Finset.range n, k) = n * (2 * (∑ k in Finset.range n, k)) := by ring
                  _ = n * (n * (n - 1)) := by rw [h₈] <;> ring
                  _ = n * (n * (n - 1)) := by ring
              have h₁₀ : n * (n * (n - 1)) = n ^ 2 * (n - 1) := by ring
              rw [h₉, h₁₀]
            have h₁₁ : n ^ 3 = 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by
              cases n with
              | zero => simp
              | succ n =>
                simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul,
                  Nat.pow_succ, Nat.mul_one, Nat.mul_assoc] at h₇ ⊢
                <;> ring_nf at h₇ ⊢ <;> nlinarith
            exact h₁₁
          nlinarith
      exact h₂ n
    exact h₁
  exact h_main n