import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
  have h₂ : 0 < a := by
    linarith [h₀.1]
  
  have h₃ : 0 < b := by
    linarith [h₀.2]
  
  have h₄ : 0 < (a + b) / 2 := by
    have h₄₁ : 0 < a + b := by linarith
    have h₄₂ : 0 < (a + b) / 2 := by positivity
    exact h₄₂
  
  have h₅ : ∀ (k : ℕ), (a - b) * (a ^ k - b ^ k) ≥ 0 := by
    intro k
    have h₅₁ : a > 0 := by linarith
    have h₅₂ : b > 0 := by linarith
    by_cases h₅₃ : a ≥ b
    · -- Case: a ≥ b
      have h₅₄ : a - b ≥ 0 := by linarith
      have h₅₅ : a ^ k ≥ b ^ k := by
        -- Since a ≥ b > 0, a^k ≥ b^k for any natural number k
        exact pow_le_pow_of_le_left (by linarith) h₅₃ k
      have h₅₆ : a ^ k - b ^ k ≥ 0 := by linarith
      have h₅₇ : (a - b) * (a ^ k - b ^ k) ≥ 0 := by
        nlinarith
      exact h₅₇
    · -- Case: a < b
      have h₅₄ : a - b < 0 := by linarith
      have h₅₅ : a ^ k ≤ b ^ k := by
        -- Since 0 < a < b, a^k ≤ b^k for any natural number k
        exact pow_le_pow_of_le_left (by linarith) (by linarith) k
      have h₅₆ : a ^ k - b ^ k ≤ 0 := by linarith
      have h₅₇ : (a - b) * (a ^ k - b ^ k) ≥ 0 := by
        nlinarith
      exact h₅₇
  
  have h₆ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    have h₆₁ : ∀ n : ℕ, 0 < n → ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
      intro n hn
      induction' hn with n hn IH
      · -- Base case: n = 1
        norm_num [pow_one]
        <;>
        (try ring_nf)
        <;>
        (try nlinarith)
      · -- Inductive step: assume the statement holds for n, prove for n + 1
        have h₆₂ : (a - b) * (a ^ n - b ^ n) ≥ 0 := h₅ n
        have h₆₃ : (a + b) / 2 > 0 := by positivity
        have h₆₄ : ((a + b) / 2) ^ (n + 1) = ((a + b) / 2) ^ n * ((a + b) / 2) := by
          ring_nf
          <;> field_simp
          <;> ring_nf
        rw [h₆₄]
        have h₆₅ : ((a + b) / 2) ^ n * ((a + b) / 2) ≤ ((a ^ n + b ^ n) / 2) * ((a + b) / 2) := by
          gcongr
          <;> linarith
        have h₆₆ : ((a ^ n + b ^ n) / 2) * ((a + b) / 2) = (a ^ n * a + a ^ n * b + b ^ n * a + b ^ n * b) / 4 := by
          ring_nf
          <;> field_simp
          <;> ring_nf
        rw [h₆₆] at h₆₅
        have h₆₇ : (a ^ (n + 1) + b ^ (n + 1)) / 2 ≥ (a ^ n * a + a ^ n * b + b ^ n * a + b ^ n * b) / 4 := by
          have h₆₈ : a ^ (n + 1) = a ^ n * a := by
            ring_nf
          have h₆₉ : b ^ (n + 1) = b ^ n * b := by
            ring_nf
          rw [h₆₈, h₆₉]
          have h₇₀ : a ^ n * a + b ^ n * b ≥ a ^ n * b + b ^ n * a := by
            nlinarith [h₅ n]
          nlinarith [h₅ n]
        have h₆₈ : ((a + b) / 2) ^ (n + 1) ≤ (a ^ (n + 1) + b ^ (n + 1)) / 2 := by
          have h₆₉ : ((a + b) / 2) ^ (n + 1) ≤ (a ^ n * a + a ^ n * b + b ^ n * a + b ^ n * b) / 4 := by
            linarith
          have h₇₀ : (a ^ (n + 1) + b ^ (n + 1)) / 2 ≥ (a ^ n * a + a ^ n * b + b ^ n * a + b ^ n * b) / 4 := by
            exact h₆₇
          have h₇₁ : ((a + b) / 2) ^ (n + 1) ≤ (a ^ (n + 1) + b ^ (n + 1)) / 2 := by
            linarith
          exact h₇₁
        simpa [pow_succ] using h₆₈
    exact h₆₁ n h₁
  exact h₆