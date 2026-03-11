import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_15 (s : ℕ → ℕ → ℕ)
    (h₀ : ∀ a b, 0 < a ∧ 0 < b → s a b = a ^ (b : ℕ) + b ^ (a : ℕ)) : s 2 6 = 100 := by
  have h₁ : s 2 6 = 2 ^ 6 + 6 ^ 2 := by
    -- Apply the given property of the function s to the arguments 2 and 6 with the conditions 0 < 2 and 0 < 6.
    have h₁ := h₀ 2 6 (by decide)
    -- Simplify the expression using the property applied to 2 and 6.
    simpa using h₁
  
  have h₂ : 2 ^ 6 = 64 := by
    -- We need to prove that 2^6 equals 64.
    -- First, we use the given property of the function s to express s 2 6 in terms of exponents.
    have h₂ : 0 < 2 ∧ 0 < 6 := by norm_num
    -- Simplify the expression using the property h₀ and the fact that both 2 and 6 are positive.
    simp_all [h₀, h₂]
    -- Now, we calculate the values of 2^6 and 6^2.
    -- 2^6 is 64, and 6^2 is 36.
    -- Adding these together gives 64 + 36 = 100.
    -- However, the problem statement tells us that s 2 6 equals 2^6 + 6^2, which simplifies to 64.
    -- This step confirms that 2^6 equals 64.
    <;> norm_num
  
  have h₃ : 6 ^ 2 = 36 := by
    simp_all [h₀]
    <;> norm_num
    <;> rfl
  
  have h₄ : 64 + 36 = 100 := by
    simp_all [h₀]
    <;> norm_num
    <;> rfl
  
  -- Using the given definitions and properties, we simplify the expression step by step.
  simp_all [h₀, h₂, h₃, h₄]
  -- Simplify the expression using the properties and the given values.
  <;> simp_all [h₀, h₂, h₃, h₄]
  -- Normalize the numbers to ensure correctness.
  <;> norm_num
  -- Use linear arithmetic to finalize the proof.
  <;> linarith