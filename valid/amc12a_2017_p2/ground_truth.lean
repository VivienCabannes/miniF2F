import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2017_p2 (x y : ℝ) (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : x + y = 4 * (x * y)) :
  1 / x + 1 / y = 4 := by
  have h₃ : x + y = 4 * (x * y) := by
    rw [h₂]
    <;> linarith
  
  have h₄ : 1 / x + 1 / y = (y + x) / (x * y) := by
    field_simp [h₀, h₁]
    <;> ring_nf
    <;> linarith
  
  have h₅ : (y + x) / (x * y) = (4 * (x * y)) / (x * y) := by
    -- Simplify the given equation using field operations and the given non-zero conditions.
    field_simp [h₀, h₁] at h₄ ⊢
    -- Normalize the equation using algebraic simplification.
    ring_nf at h₄ ⊢
    -- Use linear arithmetic to verify the equality.
    linarith
  
  have h₆ : (4 * (x * y)) / (x * y) = 4 := by
    -- We use the fact that x and y are nonzero to simplify the fractions.
    have h₆ : x * y ≠ 0 := mul_ne_zero h₀ h₁
    -- Simplify the fraction 4 * (x * y) / (x * y) to 4.
    field_simp at h₅ ⊢
    -- Since x * y ≠ 0, we can cancel x * y in the numerator and denominator.
    <;> simp_all
    -- Simplify the expression using the given conditions and the fact that x * y ≠ 0.
    <;> nlinarith
  
  have h₇ : 1 / x + 1 / y = 4 := by
    -- Simplify the given equations using the properties of real numbers and the given hypotheses.
    simp_all [div_eq_mul_inv]
    -- Use linear arithmetic to conclude the proof.
    <;> linarith
  
  -- Using the given conditions and the derived equations, we conclude that 1/x + 1/y = 4.
  simpa [h₀, h₁] using h₇