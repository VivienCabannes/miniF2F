import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_1pxpownlt1pnx
  (x : ℝ)
  (n : ℕ)
  (h₀ : -1 < x)
  (h₁ : 0 < n) :
  (1 + ↑n*x) ≤ (1 + x)^(n:ℕ) := by
  have h_base : 1 + (1 : ℝ) * x ≤ (1 + x) ^ 1 := by
    norm_num
    <;>
    (try ring_nf at * <;> linarith) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
  
  have h_inductive : ∀ (k : ℕ), 0 < k → 1 + (k : ℝ) * x ≤ (1 + x) ^ k → 1 + ((k + 1 : ℕ) : ℝ) * x ≤ (1 + x) ^ (k + 1) := by
    intro k hk_pos hk_ineq
    have h₁_pos : 0 < (1 + x : ℝ) := by linarith
    have h₂ : (1 + x : ℝ) ^ (k + 1 : ℕ) = (1 + x : ℝ) ^ k * (1 + x : ℝ) := by
      ring_nf
      <;> field_simp [h₁_pos.ne']
      <;> ring_nf
      <;> simp [pow_succ]
      <;> ring_nf
    rw [h₂]
    have h₃ : (1 + (k : ℝ) * x : ℝ) * (1 + x : ℝ) = 1 + ((k + 1 : ℕ) : ℝ) * x + (k : ℝ) * x ^ 2 := by
      ring_nf
      <;> field_simp [h₁_pos.ne']
      <;> ring_nf
      <;> simp [add_assoc, add_comm, add_left_comm]
      <;> ring_nf at *
      <;> norm_cast
      <;> ring_nf at *
      <;> field_simp [h₁_pos.ne'] at *
      <;> ring_nf at *
      <;> norm_cast at *
      <;> linarith
    have h₄ : (1 + (k : ℝ) * x : ℝ) ≤ (1 + x : ℝ) ^ k := by
      exact hk_ineq
    have h₅ : (1 + (k : ℝ) * x : ℝ) * (1 + x : ℝ) ≤ (1 + x : ℝ) ^ k * (1 + x : ℝ) := by
      exact mul_le_mul_of_nonneg_right h₄ (by linarith)
    have h₆ : 1 + ((k + 1 : ℕ) : ℝ) * x + (k : ℝ) * x ^ 2 ≤ (1 + x : ℝ) ^ k * (1 + x : ℝ) := by
      linarith [sq_nonneg (x : ℝ)]
    have h₇ : 1 + ((k + 1 : ℕ) : ℝ) * x ≤ (1 + x : ℝ) ^ k * (1 + x : ℝ) := by
      have h₈ : (k : ℝ) * x ^ 2 ≥ 0 := by
        have h₉ : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
        have h₁₀ : x ^ 2 ≥ 0 := by nlinarith
        nlinarith
      linarith
    exact h₇
    <;> norm_num at *
    <;> linarith
  
  have h_main : 1 + (n : ℝ) * x ≤ (1 + x) ^ n := by
    have h₂ : ∀ (k : ℕ), 0 < k → 1 + (k : ℝ) * x ≤ (1 + x) ^ k := by
      intro k hk_pos
      induction' hk_pos with k hk_pos IH
      · -- Base case: k = 1
        simpa using h_base
      · -- Inductive step: assume the statement holds for k, prove for k + 1
        simpa using h_inductive k hk_pos IH
    have h₃ : 0 < n := h₁
    have h₄ : 1 + (n : ℝ) * x ≤ (1 + x) ^ n := h₂ n h₃
    exact h₄
    <;> norm_num at *
    <;> linarith
  
  simpa using h_main