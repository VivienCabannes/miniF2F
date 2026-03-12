import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 800000

theorem imo_1962_p4 (S : Set ℝ)
    (h₀ : S = { x : ℝ | Real.cos x ^ 2 + Real.cos (2 * x) ^ 2 + Real.cos (3 * x) ^ 2 = 1 }) :
    S =
      { x : ℝ |
        ∃ m : ℤ,
          x = π / 2 + m * π ∨
            x = π / 4 + m * π / 2 ∨ x = π / 6 + m * π ∨ x = 5 * π / 6 + m * π } := by
  subst h₀
  ext x
  simp only [Set.mem_setOf_eq]
  -- Key algebraic identity: for any a in a commutative ring with no zero divisors,
  -- a^2 + (2a^2-1)^2 + (4a^3-3a)^2 = 1 ↔ (2a^2-1)*(4a^3-3a) = 0
  have formula : ∀ a : ℝ,
      a ^ 2 + (2 * a ^ 2 - 1) ^ 2 + (4 * a ^ 3 - 3 * a) ^ 2 = 1 ↔
        (2 * a ^ 2 - 1) * (4 * a ^ 3 - 3 * a) = 0 := by
    intro a
    constructor
    · intro h
      have hsq : ((2 * a ^ 2 - 1) * (4 * a ^ 3 - 3 * a)) ^ 2 = 0 := by nlinarith
      have := sq_eq_zero_iff.mp hsq
      exact this
    · intro h
      linear_combination 2 * a * h
  -- Rewrite using cos_two_mul and cos_three_mul
  have key : Real.cos x ^ 2 + Real.cos (2 * x) ^ 2 + Real.cos (3 * x) ^ 2 = 1 ↔
      Real.cos (2 * x) = 0 ∨ Real.cos (3 * x) = 0 := by
    rw [Real.cos_two_mul, cos_three_mul]
    rw [formula (Real.cos x)]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · left; linarith
      · right; linarith
    · intro h
      rcases h with h1 | h1
      · apply mul_eq_zero_of_left; linarith
      · apply mul_eq_zero_of_right; linarith
  -- Solve cos(2x) = 0
  have solve_cos2x : Real.cos (2 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 := by
    rw [Real.cos_eq_zero_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by linarith⟩
  -- Solve cos(3x) = 0
  have solve_cos3x : Real.cos (3 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 6 := by
    rw [Real.cos_eq_zero_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by linarith⟩
  rw [key, solve_cos2x, solve_cos3x]
  -- Now we need: (∃ k, x = (2k+1)π/4) ∨ (∃ k, x = (2k+1)π/6) ↔
  --              ∃ m, x = π/2+mπ ∨ x = π/4+mπ/2 ∨ x = π/6+mπ ∨ x = 5π/6+mπ
  constructor
  · -- Forward: Mathlib form → local form
    rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · -- x = (2k+1)π/4 = π/4 + kπ/2, which is the second case with m = k
      refine ⟨k, Or.inr (Or.inl ?_)⟩
      have : (2 * (k : ℝ) + 1) * π / 4 = π / 4 + ↑k * π / 2 := by ring
      linarith
    · -- x = (2k+1)π/6, need case analysis on k mod 3
      have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · -- k = 3j, x = (6j+1)π/6 = π/6 + jπ
        obtain ⟨j, hj⟩ : ∃ j : ℤ, k = 3 * j := ⟨k / 3, by omega⟩
        refine ⟨j, Or.inr (Or.inr (Or.inl ?_))⟩
        have : (2 * (k : ℝ) + 1) * π / 6 = π / 6 + ↑j * π := by
          rw [hj]; push_cast; ring
        linarith
      · -- k = 3j+1, x = (6j+3)π/6 = π/2 + jπ
        obtain ⟨j, hj⟩ : ∃ j : ℤ, k = 3 * j + 1 := ⟨(k - 1) / 3, by omega⟩
        refine ⟨j, Or.inl ?_⟩
        have : (2 * (k : ℝ) + 1) * π / 6 = π / 2 + ↑j * π := by
          rw [hj]; push_cast; ring
        linarith
      · -- k = 3j+2, x = (6j+5)π/6 = 5π/6 + jπ
        obtain ⟨j, hj⟩ : ∃ j : ℤ, k = 3 * j + 2 := ⟨(k - 2) / 3, by omega⟩
        refine ⟨j, Or.inr (Or.inr (Or.inr ?_))⟩
        have : (2 * (k : ℝ) + 1) * π / 6 = 5 * π / 6 + ↑j * π := by
          rw [hj]; push_cast; ring
        linarith
  · -- Backward: local form → Mathlib form
    rintro ⟨m, hm1 | hm2 | hm3 | hm4⟩
    · -- x = π/2 + mπ = (2(3m+1)+1)π/6 = (6m+3)π/6
      right
      refine ⟨3 * m + 1, ?_⟩
      have : (2 * ((3 * m + 1 : ℤ) : ℝ) + 1) * π / 6 = π / 2 + ↑m * π := by
        push_cast; ring
      linarith
    · -- x = π/4 + mπ/2 = (2m+1)π/4
      left
      refine ⟨m, ?_⟩
      have : (2 * (m : ℝ) + 1) * π / 4 = π / 4 + ↑m * π / 2 := by ring
      linarith
    · -- x = π/6 + mπ = (2(3m)+1)π/6 = (6m+1)π/6
      right
      refine ⟨3 * m, ?_⟩
      have : (2 * ((3 * m : ℤ) : ℝ) + 1) * π / 6 = π / 6 + ↑m * π := by
        push_cast; ring
      linarith
    · -- x = 5π/6 + mπ = (2(3m+2)+1)π/6 = (6m+5)π/6
      right
      refine ⟨3 * m + 2, ?_⟩
      have : (2 * ((3 * m + 2 : ℤ) : ℝ) + 1) * π / 6 = 5 * π / 6 + ↑m * π := by
        push_cast; ring
      linarith
