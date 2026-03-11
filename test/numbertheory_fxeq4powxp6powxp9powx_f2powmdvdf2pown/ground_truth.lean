import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown
  (m n : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ x, f x = 4^x + 6^x + 9^x)
  (h₁ : 0 < m ∧ 0 < n)
  (h₂ : m ≤ n) :
  f (2^m)∣f (2^n) := by
  have h_main : ∀ k : ℕ, f (2 * k) = f k * (f k - 2 * 6 ^ k) := by
    intro k
    have h₁ : f (2 * k) = 4 ^ (2 * k) + 6 ^ (2 * k) + 9 ^ (2 * k) := by
      rw [h₀]
    have h₂ : f k = 4 ^ k + 6 ^ k + 9 ^ k := by
      rw [h₀]
    rw [h₁, h₂]
    have h₃ : (4 : ℕ) ^ (2 * k) = (4 : ℕ) ^ k * (4 : ℕ) ^ k := by
      rw [show (2 * k : ℕ) = k + k by ring]
      rw [pow_add]
      <;> ring
    have h₄ : (6 : ℕ) ^ (2 * k) = (6 : ℕ) ^ k * (6 : ℕ) ^ k := by
      rw [show (2 * k : ℕ) = k + k by ring]
      rw [pow_add]
      <;> ring
    have h₅ : (9 : ℕ) ^ (2 * k) = (9 : ℕ) ^ k * (9 : ℕ) ^ k := by
      rw [show (2 * k : ℕ) = k + k by ring]
      rw [pow_add]
      <;> ring
    rw [h₃, h₄, h₅]
    have h₆ : (4 : ℕ) ^ k * (4 : ℕ) ^ k + (6 : ℕ) ^ k * (6 : ℕ) ^ k + (9 : ℕ) ^ k * (9 : ℕ) ^ k = ((4 : ℕ) ^ k + (6 : ℕ) ^ k + (9 : ℕ) ^ k) * ((4 : ℕ) ^ k + (6 : ℕ) ^ k + (9 : ℕ) ^ k) - 2 * ((4 : ℕ) ^ k * (6 : ℕ) ^ k + (4 : ℕ) ^ k * (9 : ℕ) ^ k + (6 : ℕ) ^ k * (9 : ℕ) ^ k) := by
      have h₇ : ((4 : ℕ) ^ k + (6 : ℕ) ^ k + (9 : ℕ) ^ k) * ((4 : ℕ) ^ k + (6 : ℕ) ^ k + (9 : ℕ) ^ k) = (4 : ℕ) ^ k * (4 : ℕ) ^ k + (6 : ℕ) ^ k * (6 : ℕ) ^ k + (9 : ℕ) ^ k * (9 : ℕ) ^ k + 2 * ((4 : ℕ) ^ k * (6 : ℕ) ^ k + (4 : ℕ) ^ k * (9 : ℕ) ^ k + (6 : ℕ) ^ k * (9 : ℕ) ^ k) := by
        ring
      have h₈ : (4 : ℕ) ^ k * (6 : ℕ) ^ k + (4 : ℕ) ^ k * (9 : ℕ) ^ k + (6 : ℕ) ^ k * (9 : ℕ) ^ k = (6 : ℕ) ^ k * ((4 : ℕ) ^ k + (9 : ℕ) ^ k) + (4 : ℕ) ^ k * (9 : ℕ) ^ k := by
        ring
      omega
    have h₇ : (4 : ℕ) ^ k * (6 : ℕ) ^ k + (4 : ℕ) ^ k * (9 : ℕ) ^ k + (6 : ℕ) ^ k * (9 : ℕ) ^ k = (6 : ℕ) ^ k * ((4 : ℕ) ^ k + (6 : ℕ) ^ k + (9 : ℕ) ^ k) := by
      have h₈ : (4 : ℕ) ^ k * (6 : ℕ) ^ k + (4 : ℕ) ^ k * (9 : ℕ) ^ k + (6 : ℕ) ^ k * (9 : ℕ) ^ k = (6 : ℕ) ^ k * ((4 : ℕ) ^ k + (9 : ℕ) ^ k) + (4 : ℕ) ^ k * (9 : ℕ) ^ k := by
        ring
      have h₉ : (6 : ℕ) ^ k * ((4 : ℕ) ^ k + (9 : ℕ) ^ k) + (4 : ℕ) ^ k * (9 : ℕ) ^ k = (6 : ℕ) ^ k * ((4 : ℕ) ^ k + (6 : ℕ) ^ k + (9 : ℕ) ^ k) := by
        have h₁₀ : (6 : ℕ) ^ k = (2 : ℕ) ^ k * (3 : ℕ) ^ k := by
          rw [show (6 : ℕ) = 2 * 3 by norm_num]
          rw [mul_pow]
          <;> ring
        rw [h₁₀]
        have h₁₁ : (4 : ℕ) ^ k = (2 : ℕ) ^ (2 * k) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
          rw [← pow_mul]
          <;> ring_nf
        have h₁₂ : (9 : ℕ) ^ k = (3 : ℕ) ^ (2 * k) := by
          rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
          rw [← pow_mul]
          <;> ring_nf
        rw [h₁₁, h₁₂]
        have h₁₃ : (2 : ℕ) ^ k * (3 : ℕ) ^ k * ((2 : ℕ) ^ (2 * k) + (3 : ℕ) ^ (2 * k)) + (2 : ℕ) ^ (2 * k) * (3 : ℕ) ^ (2 * k) = (2 : ℕ) ^ k * (3 : ℕ) ^ k * ((2 : ℕ) ^ (2 * k) + (2 : ℕ) ^ k * (3 : ℕ) ^ k + (3 : ℕ) ^ (2 * k)) := by
          have h₁₄ : (2 : ℕ) ^ (2 * k) = (2 : ℕ) ^ k * (2 : ℕ) ^ k := by
            rw [show (2 * k : ℕ) = k + k by ring]
            rw [pow_add]
            <;> ring
          have h₁₅ : (3 : ℕ) ^ (2 * k) = (3 : ℕ) ^ k * (3 : ℕ) ^ k := by
            rw [show (2 * k : ℕ) = k + k by ring]
            rw [pow_add]
            <;> ring
          rw [h₁₄, h₁₅]
          ring_nf
          <;> nlinarith [pow_pos (by norm_num : 0 < (2 : ℕ)) k, pow_pos (by norm_num : 0 < (3 : ℕ)) k]
        rw [h₁₃]
        <;> ring_nf
        <;> nlinarith [pow_pos (by norm_num : 0 < (2 : ℕ)) k, pow_pos (by norm_num : 0 < (3 : ℕ)) k]
      omega
    rw [h₆, h₇]
    <;> cases k with
    | zero =>
      norm_num [h₀, pow_zero, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
    | succ k =>
      simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
      <;> ring_nf at *
      <;> norm_num at *
      <;> omega
  
  have h_div : ∀ k : ℕ, f k ∣ f (2 * k) := by
    intro k
    have h₁ : f (2 * k) = f k * (f k - 2 * 6 ^ k) := h_main k
    rw [h₁]
    exact ⟨f k - 2 * 6 ^ k, by
      cases k with
      | zero =>
        simp [h₀, pow_zero, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
      | succ k =>
        simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
        <;> ring_nf at *
        <;> norm_num at *
        <;> omega
    ⟩
  
  have h_chain : ∀ t : ℕ, f (2 ^ m) ∣ f (2 ^ (m + t)) := by
    intro t
    have h₃ : ∀ t : ℕ, f (2 ^ m) ∣ f (2 ^ (m + t)) := by
      intro t
      induction' t with t ih
      · -- Base case: t = 0
        simp [h₀]
      · -- Inductive step: assume the statement holds for t, prove for t + 1
        have h₄ : f (2 ^ (m + t)) ∣ f (2 * 2 ^ (m + t)) := h_div _
        have h₅ : f (2 * 2 ^ (m + t)) = f (2 ^ (m + t + 1)) := by
          rw [show (2 * 2 ^ (m + t) : ℕ) = 2 ^ (m + t + 1) by
            ring_nf
            <;> simp [pow_add, pow_one, mul_add, mul_one, add_mul, one_mul]]
        rw [h₅] at h₄
        have h₆ : m + t + 1 = m + (t + 1) := by ring
        rw [h₆] at h₄
        exact dvd_trans ih h₄
    exact h₃ t
  
  have h_final : f (2 ^ m) ∣ f (2 ^ n) := by
    have h₃ : ∃ t, n = m + t := by
      use n - m
      have h₄ : m ≤ n := h₂
      have h₅ : n - m + m = n := by
        have h₆ : m ≤ n := h₂
        have h₇ : n - m + m = n := by
          omega
        exact h₇
      omega
    obtain ⟨t, ht⟩ := h₃
    have h₄ : f (2 ^ m) ∣ f (2 ^ (m + t)) := h_chain t
    have h₅ : f (2 ^ (m + t)) = f (2 ^ n) := by
      rw [ht]
      <;> simp [pow_add]
      <;> ring_nf
    rw [h₅] at h₄
    exact h₄
  
  exact h_final