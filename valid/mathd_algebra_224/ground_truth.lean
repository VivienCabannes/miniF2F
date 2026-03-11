import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_224 (S : Finset ℕ)
  (h₀ : ∀ n : ℕ, n ∈ S ↔ Real.sqrt n < 7 / 2 ∧ 2 < Real.sqrt n) : S.card = 8 := by
  have h1 : ∀ n ∈ S, n > 4 ∧ n < 13 := by
    -- Introduce a natural number `n` and assume it is in the set `S`.
    intro n h₁
    -- Simplify the membership condition using the given property `h₀`.
    simp only [h₀, Finset.mem_filter, Finset.mem_univ, true_and_iff] at h₁
    -- Extract the inequality conditions from the simplified membership condition.
    have h₂ := h₁.1
    have h₃ := h₁.2
    -- Prove that `n > 4` by squaring the inequality `2 < Real.sqrt n`.
    have h₄ : (4 : ℝ) < n := by
      nlinarith [sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
    have h₅ : (n : ℝ) < 13 := by
      nlinarith [sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
    -- Conclude the proof by showing `n > 4` and `n < 13`.
    exact ⟨by exact_mod_cast h₄, by exact_mod_cast h₅⟩
  
  have h2 : ∀ n : ℕ, 4 < n ∧ n < 13 → n ∈ S := by
    intro n hn
    have h2 : n ∈ S ↔ Real.sqrt n < 7 / 2 ∧ 2 < Real.sqrt n := h₀ n
    simp_all only [Finset.mem_filter, Finset.mem_univ, true_and_iff, and_imp]
    -- We need to show that each n in the range (4, 13) is in S.
    -- This involves checking that each n satisfies the condition of S.
    -- The condition is that the square root of n is between 2 and 3.5.
    -- We use the fact that the square roots of integers are known to verify this.
    norm_num
    <;> rcases hn with ⟨h3, h4⟩
    <;> interval_cases n <;> norm_num [Real.sqrt_lt, Real.lt_sqrt] at * <;> linarith
  
  have h3 : S = {5, 6, 7, 8, 9, 10, 11, 12} := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀, true_and, and_true] at *
    constructor
    -- We need to show that if n is in S, then n is one of the elements 5, 6, 7, 8, 9, 10, 11, 12.
    intro h
    have h3 := h1 n h
    have h4 := h2 n
    have h5 : n < 13 := h3.2
    have h6 : 4 < n := h3.1
    interval_cases n <;> simp_all
    -- We need to show that if n is one of the elements 5, 6, 7, 8, 9, 10, 11, 12, then n is in S.
    intro h
    have h3 : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 := by simp_all
    rcases h3 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp_all
    <;> norm_num [Real.sqrt_lt, Real.lt_sqrt]
    <;> linarith
  
  have h4 : S.card = 8 := by
    -- Simplify the given conditions and the final set S
    simp_all only [Finset.card_insert_of_not_mem, Finset.mem_singleton, Finset.card_singleton,
      Finset.card_empty, Nat.cast_ofNat]
    -- Normalize the numbers to ensure correctness
    <;> norm_num
    <;> aesop
  
  simpa [h3, h4] using h2 5 ⟨by norm_num, by norm_num⟩