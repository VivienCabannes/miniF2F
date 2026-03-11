import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_158
  (a : ℕ)
  (h₀ : Even a)
  (h₁ : ∑ k ∈ Finset.range 8, (2 * k + 1) - ∑ k ∈ Finset.range 5, (a + 2 * k) = (4:ℤ)) :
  a = 8 := by
  have h₂ : ∑ k in Finset.range 8, (2 * k + 1 : ℕ) = 64 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    <;> rfl
  
  have h₃ : ∑ k in Finset.range 5, (a + 2 * k : ℕ) = 5 * a + 20 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Nat.mul_add, Nat.add_assoc, Nat.add_mul]
    <;> ring_nf at *
    <;> norm_num at *
    <;> omega
  
  have h₄ : a = 8 := by
    have h₅ : (∑ k in Finset.range 8, 2 * k + 1 : ℕ) = 64 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h₂ ⊢
      <;> simp_all [Finset.sum_range_succ, Nat.even_iff]
      <;> ring_nf at *
      <;> norm_num at *
      <;> omega
    have h₆ : (∑ k in Finset.range 5, a + 2 * k : ℕ) = 5 * a + 20 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Nat.mul_add, Nat.add_assoc, Nat.add_mul] at h₃ ⊢
      <;> ring_nf at *
      <;> norm_num at *
      <;> omega
    have h₇ : (64 : ℤ) - (5 * a + 20 : ℤ) = (4 : ℤ) := by
      have h₇₁ : (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) = (64 : ℤ) := by
        norm_cast
        <;> simp_all [Finset.sum_range_succ, Nat.even_iff]
        <;> ring_nf at *
        <;> norm_num at *
        <;> omega
      have h₇₂ : (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (5 * a + 20 : ℤ) := by
        norm_cast
        <;> simp_all [Finset.sum_range_succ, Nat.even_iff]
        <;> ring_nf at *
        <;> norm_num at *
        <;> omega
      have h₇₃ : (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) - (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (4 : ℤ) := by
        simpa using h₁
      rw [h₇₁, h₇₂] at h₇₃
      <;> linarith
    have h₈ : a = 8 := by
      have h₈₁ : (a : ℤ) = 8 := by
        have h₈₂ : (64 : ℤ) - (5 * a + 20 : ℤ) = (4 : ℤ) := by simpa using h₇
        have h₈₃ : (5 : ℤ) * a + 20 = 60 := by linarith
        have h₈₄ : (a : ℤ) = 8 := by
          ring_nf at h₈₃ ⊢
          <;> norm_cast at h₈₃ ⊢
          <;> omega
        simpa using h₈₄
      have h₈₂ : a = 8 := by
        norm_cast at h₈₁
        <;> omega
      exact h₈₂
    exact h₈
  
  apply h₄