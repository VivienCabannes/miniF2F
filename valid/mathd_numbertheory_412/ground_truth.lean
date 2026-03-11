import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_412 (x y : ℤ) (h₀ : x % 19 = 4) (h₁ : y % 19 = 7) :
  (x + 1) ^ 2 * (y + 5) ^ 3 % 19 = 13 := by
  have hx_add_1 : (x + 1) % 19 = 5 := by
    -- Use the properties of modular arithmetic to simplify the expression.
    simp [h₀, h₁, Int.add_emod, Int.mul_emod, Int.emod_emod, Int.add_assoc]
    -- Simplify the expression using numerical computations.
    <;> norm_num
    <;> rfl
  
  have hx_sq : (x + 1) ^ 2 % 19 = 6 := by
    have h₂ : (x + 1) ^ 2 % 19 = 6 := by
      -- Expand the square of (x + 1)
      rw [sq]
      -- Normalize the expression modulo 19 using the given congruences
      norm_num [Int.mul_emod, hx_add_1, h₀, h₁, Int.add_emod, Int.mul_emod]
    -- Use the derived result to conclude the proof
    assumption
  
  have hy_add_5 : (y + 5) % 19 = 12 := by
    have h₂ := congr_arg (· % 19) hx_sq
    have h₃ := congr_arg (· % 19) hx_add_1
    have h₄ := congr_arg (· % 19) h₀
    have h₅ := congr_arg (· % 19) h₁
    -- Simplify the expressions modulo 19
    norm_num at h₂ h₃ h₄ h₅
    -- Use the omega tactic to solve the resulting system of linear congruences
    omega
  
  have hy_cubed : (y + 5) ^ 3 % 19 = 18 := by
    have h₂ := congr_arg (· % 19) (pow_three (y + 5))
    simp at h₂
    simp_all [Int.mul_emod, Int.add_emod, pow_three]
    -- We need to show that (y + 5)^3 % 19 = 18.
    -- We know that y % 19 = 7 and y + 5 % 19 = 12.
    -- We will compute (y + 5)^3 % 19 step by step.
    -- (y + 5)^3 = (7 + 5)^3 = 12^3 = 1728.
    -- 1728 % 19 = 18.
    -- Therefore, (y + 5)^3 % 19 = 18.
    <;> omega
  
  have h_product : (x + 1) ^ 2 * (y + 5) ^ 3 % 19 = 13 := by
    -- Simplify the expression using the given congruences and properties of modular arithmetic.
    norm_num [Int.mul_emod, hx_sq, hy_cubed, Int.add_emod]
    -- Verify the final result by direct computation.
    <;> decide
  
  -- Use the given properties and modular arithmetic rules to simplify and verify the final product.
  norm_num [Int.mul_emod, Int.add_emod, pow_two, pow_three] at hx_add_1 hx_sq hy_add_5 hy_cubed h_product ⊢
  -- Use the `omega` tactic to solve the resulting system of linear equations.
  <;> omega