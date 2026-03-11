import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2
  (n : ℕ)
  (h₀ : 0 < n) :
  (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := by
  have h_main : ∃ (k : ℕ), 3 ^ 2 ^ n = 1 + 2 ^ (n + 2) + k * 2 ^ (n + 3) := by
    have h₁ : ∀ n : ℕ, 0 < n → ∃ (k : ℕ), 3 ^ 2 ^ n = 1 + 2 ^ (n + 2) + k * 2 ^ (n + 3) := by
      intro n hn
      induction' hn with n hn IH
      · -- Base case: n = 1
        use 0
        norm_num
      · -- Inductive step: assume the statement holds for n, prove for n + 1
        obtain ⟨k, hk⟩ := IH
        use (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) / 2 ^ (n + 4)
        have h₂ : 3 ^ 2 ^ (n + 1) = (3 ^ 2 ^ n) ^ 2 := by
          simp [pow_succ, pow_mul, pow_two]
          <;> ring_nf
          <;> simp [pow_add, pow_mul, pow_two]
          <;> ring_nf
        rw [h₂, hk]
        have h₃ : (1 + 2 ^ (n + 2) + k * 2 ^ (n + 3)) ^ 2 = 1 + 2 ^ (n + 3) + (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) := by
          have h₄ : n ≥ 0 := by linarith
          have h₅ : 2 * n + 4 ≥ n + 4 := by
            omega
          have h₆ : 2 * n + 6 ≥ n + 4 := by
            omega
          have h₇ : 2 * n + 5 ≥ n + 4 := by
            omega
          calc
            (1 + 2 ^ (n + 2) + k * 2 ^ (n + 3)) ^ 2 = 1 + 2 ^ (n + 3) + (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) := by
              ring_nf at *
              <;>
                simp [pow_add, pow_mul, mul_assoc, mul_comm, mul_left_comm, Nat.mul_div_cancel_left]
              <;>
                ring_nf at *
              <;>
                omega
            _ = 1 + 2 ^ (n + 3) + (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) := by
              rfl
        rw [h₃]
        have h₄ : (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) % 2 ^ (n + 4) = 0 := by
          have h₅ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 4) := by
            apply pow_dvd_pow 2
            omega
          have h₆ : 2 ^ (n + 4) ∣ k * 2 ^ (n + 4) := by
            exact ⟨k, by ring⟩
          have h₇ : 2 ^ (n + 4) ∣ k ^ 2 * 2 ^ (2 * n + 6) := by
            have h₈ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 6) := by
              apply pow_dvd_pow 2
              omega
            have h₉ : 2 ^ (n + 4) ∣ k ^ 2 * 2 ^ (2 * n + 6) := by
              exact dvd_mul_of_dvd_right h₈ _
            exact h₉
          have h₈ : 2 ^ (n + 4) ∣ 2 * k * 2 ^ (2 * n + 5) := by
            have h₉ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 5) := by
              apply pow_dvd_pow 2
              omega
            have h₁₀ : 2 ^ (n + 4) ∣ 2 * k * 2 ^ (2 * n + 5) := by
              have h₁₁ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 5) := h₉
              have h₁₂ : 2 ^ (n + 4) ∣ 2 * k * 2 ^ (2 * n + 5) := by
                calc
                  2 ^ (n + 4) ∣ 2 ^ (2 * n + 5) := h₁₁
                  _ ∣ 2 * k * 2 ^ (2 * n + 5) := by
                    exact ⟨2 * k, by ring⟩
              exact h₁₂
            exact h₁₀
          have h₉ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5) := by
            have h₁₀ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 4) := h₅
            have h₁₁ : 2 ^ (n + 4) ∣ k * 2 ^ (n + 4) := h₆
            have h₁₂ : 2 ^ (n + 4) ∣ k ^ 2 * 2 ^ (2 * n + 6) := h₇
            have h₁₃ : 2 ^ (n + 4) ∣ 2 * k * 2 ^ (2 * n + 5) := h₈
            -- Sum of multiples is a multiple
            exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_add h₁₀ h₆) h₇) h₈
          have h₁₀ : (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) % 2 ^ (n + 4) = 0 := by
            have h₁₁ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5) := h₉
            have h₁₂ : (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) % 2 ^ (n + 4) = 0 := by
              exact Nat.mod_eq_zero_of_dvd h₁₁
            exact h₁₂
          exact h₁₀
        have h₅ : (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) / 2 ^ (n + 4) * 2 ^ (n + 4) = (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) := by
          have h₆ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5) := by
            have h₇ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 4) := by
              apply pow_dvd_pow 2
              omega
            have h₈ : 2 ^ (n + 4) ∣ k * 2 ^ (n + 4) := by
              exact ⟨k, by ring⟩
            have h₉ : 2 ^ (n + 4) ∣ k ^ 2 * 2 ^ (2 * n + 6) := by
              have h₁₀ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 6) := by
                apply pow_dvd_pow 2
                omega
              have h₁₁ : 2 ^ (n + 4) ∣ k ^ 2 * 2 ^ (2 * n + 6) := by
                exact dvd_mul_of_dvd_right h₁₀ _
              exact h₁₁
            have h₁₀ : 2 ^ (n + 4) ∣ 2 * k * 2 ^ (2 * n + 5) := by
              have h₁₁ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 5) := by
                apply pow_dvd_pow 2
                omega
              have h₁₂ : 2 ^ (n + 4) ∣ 2 * k * 2 ^ (2 * n + 5) := by
                have h₁₃ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 5) := h₁₁
                have h₁₄ : 2 ^ (n + 4) ∣ 2 * k * 2 ^ (2 * n + 5) := by
                  calc
                    2 ^ (n + 4) ∣ 2 ^ (2 * n + 5) := h₁₃
                    _ ∣ 2 * k * 2 ^ (2 * n + 5) := by
                      exact ⟨2 * k, by ring⟩
                exact h₁₄
              exact h₁₂
            -- Sum of multiples is a multiple
            exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_add h₇ h₈) h₉) h₁₀
          have h₁₁ : (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) / 2 ^ (n + 4) * 2 ^ (n + 4) = (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) := by
            have h₁₂ : 2 ^ (n + 4) ∣ 2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5) := h₆
            have h₁₃ : (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) / 2 ^ (n + 4) * 2 ^ (n + 4) = (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) := by
              exact Nat.div_mul_cancel h₁₂
            exact h₁₃
          exact h₁₁
        have h₆ : 1 + 2 ^ (n + 3) + (2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) = 1 + 2 ^ (n + 1 + 2) + ((2 ^ (2 * n + 4) + k * 2 ^ (n + 4) + k ^ 2 * 2 ^ (2 * n + 6) + 2 * k * 2 ^ (2 * n + 5)) / 2 ^ (n + 4) * 2 ^ (n + 1 + 3)) := by
          have h₇ : n + 3 = n + 1 + 2 := by ring
          have h₈ : n + 4 = n + 1 + 3 := by ring
          have h₉ : 2 * n + 4 = 2 * n + 4 := by ring
          simp [h₇, h₈, h₉, pow_add, pow_mul, Nat.mul_div_assoc, Nat.div_eq_of_lt] at h₄ h₅ ⊢ <;> ring_nf at h₄ h₅ ⊢ <;> omega
        rw [h₆]
        <;> simp [h₅, Nat.mul_div_assoc, Nat.div_eq_of_lt] <;> ring_nf at * <;> omega
    exact h₁ n h₀
  
  have h_final : (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = 2 ^ (n + 2) := by
    obtain ⟨k, hk⟩ := h_main
    have h₁ : 3 ^ 2 ^ n - 1 = 2 ^ (n + 2) + k * 2 ^ (n + 3) := by
      have h₂ : 3 ^ 2 ^ n = 1 + 2 ^ (n + 2) + k * 2 ^ (n + 3) := by linarith
      have h₃ : 3 ^ 2 ^ n - 1 = 2 ^ (n + 2) + k * 2 ^ (n + 3) := by
        have h₄ : 3 ^ 2 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          <;> positivity
        omega
      exact h₃
    rw [h₁]
    have h₂ : (2 ^ (n + 2) + k * 2 ^ (n + 3)) % 2 ^ (n + 3) = 2 ^ (n + 2) % 2 ^ (n + 3) := by
      have h₃ : (2 ^ (n + 2) + k * 2 ^ (n + 3)) % 2 ^ (n + 3) = (2 ^ (n + 2)) % 2 ^ (n + 3) := by
        have h₄ : k * 2 ^ (n + 3) % 2 ^ (n + 3) = 0 := by
          have h₅ : 2 ^ (n + 3) ∣ k * 2 ^ (n + 3) := by
            use k
            <;> ring
          exact Nat.mod_eq_zero_of_dvd h₅
        have h₅ : (2 ^ (n + 2) + k * 2 ^ (n + 3)) % 2 ^ (n + 3) = (2 ^ (n + 2) % 2 ^ (n + 3) + k * 2 ^ (n + 3) % 2 ^ (n + 3)) % 2 ^ (n + 3) := by
          simp [Nat.add_mod]
        rw [h₅]
        have h₆ : k * 2 ^ (n + 3) % 2 ^ (n + 3) = 0 := h₄
        rw [h₆]
        have h₇ : (2 ^ (n + 2) % 2 ^ (n + 3) + 0) % 2 ^ (n + 3) = 2 ^ (n + 2) % 2 ^ (n + 3) := by
          simp [Nat.add_mod]
        rw [h₇]
      exact h₃
    rw [h₂]
    have h₃ : 2 ^ (n + 2) % 2 ^ (n + 3) = 2 ^ (n + 2) := by
      have h₄ : 2 ^ (n + 2) < 2 ^ (n + 3) := by
        apply Nat.pow_lt_pow_of_lt_right
        <;> omega
      have h₅ : 2 ^ (n + 2) % 2 ^ (n + 3) = 2 ^ (n + 2) := by
        rw [Nat.mod_eq_of_lt h₄]
      rw [h₅]
    rw [h₃]
  
  exact h_final