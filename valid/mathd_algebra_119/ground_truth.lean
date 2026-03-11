import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_119 (d e : ℝ) (h₀ : 2 * d = 17 * e - 8) (h₁ : 2 * e = d - 9) : e = 2 := by
  have hd : d = 2 * e + 9 := by
    -- Start with the second equation and manipulate it to solve for d.
    have h₀' := h₀
    -- Simplify the first equation by expanding and rearranging terms.
    ring_nf at h₀' h₁ ⊢
    -- Use linear arithmetic to solve the simplified system of equations.
    linarith
  
  have h_substituted : 2 * (2 * e + 9) = 17 * e - 8 := by
    -- Substitute the expression for d from the third equation into the first equation.
    rw [hd] at h₀
    -- Simplify the equation to show that 2 * (2 * e + 9) = 17 * e - 8.
    linarith
  
  have h_simplified : 4 * e + 18 = 17 * e - 8 := by
    -- Simplify the substituted equation to match the target equation
    linarith
    <;> linarith
    <;> linarith
    <;> linarith
  
  have h_e : e = 2 := by
    have h₂ : e = 2 := by linarith
    exact h₂
  
  have h_verify₁ : 2 * d = 17 * 2 - 8 := by
    subst hd
    linarith
  
  have h_verify₂ : 2 * 2 = d - 9 := by
    -- Substitute the expression for d from the second equation into the first equation.
    subst d
    -- Simplify the equation and solve for e.
    linarith
  
  -- The given value of e is 2, which we need to verify.
  have h₂ : e = 2 := h_e
  -- Using the verified values, we confirm that e = 2.
  linarith