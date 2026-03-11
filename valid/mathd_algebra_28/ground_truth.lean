import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_28 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x ^ 2 + 5 * x + c)
  (h₁ : ∃ x, f x ≤ 0) : c ≤ 25 / 8 := by
  have D_eq : 5^2 - 4 * 2 * c = 25 - 8 * c := by
    -- We start by simplifying the given expression 5^2 - 4 * 2 * c
    norm_num
    -- Simplify the expression using specific algebraic rules and properties
    <;> ring_nf
    -- Simplify further using the properties of multiplication and addition
    <;> simp_all [mul_assoc]
    -- Normalize the numerical values to achieve the final simplified form
    <;> norm_num
    -- Use linear arithmetic to conclude the proof
    <;> linarith
  
  have D_nonneg : 25 - 8 * c ≥ 0 := by
    -- Simplify the discriminant expression and prepare for further analysis.
    have h₂ := h₁
    cases' h₂ with x hx
    -- Use the definition of the function to substitute and simplify the inequality.
    simp only [h₀, mul_assoc, mul_comm, mul_left_comm] at hx
    -- Use the fact that the function values are non-negative to derive the inequality.
    linarith [sq_nonneg (x + (5 / 4)), sq_nonneg (x - (5 / 4))]
  
  have c_le : c ≤ 25 / 8 := by
    -- Use the fact that the discriminant is non-negative to derive the inequality for c.
    cases' h₁ with x hx
    -- Use the non-negativity of the discriminant to derive the inequality for c.
    linarith [sq_nonneg (x + (5 : ℝ) / 4), h₀ x, h₀ (x + (5 : ℝ) / 4)]
  
  linarith