import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_326 (n : ℤ) (h₀ : (n - 1) * n * (n + 1) = 720 ) : n + 1 = 10 := by
  have h₁ : (n - 1) * n * (n + 1) = n^3 - n := by
    -- Simplify the given equation to show that (n - 1) * n * (n + 1) = n^3 - n
    nlinarith [sq_nonneg (n - 1), sq_nonneg n, sq_nonneg (n + 1), sq_nonneg (n - 1 + n + 1)]
  
  have h₂ : n^3 - n = 720 := by
    linarith
  
  have h₃ : n = 9 := by
    -- We need to solve for n in the equation n^3 - n = 720.
    have h₃ : n = 9 := by
      -- Use the fact that n^3 - n = 720 and the symmetry in the equation to find n = 9.
      nlinarith [sq_nonneg (n - 9), sq_nonneg (n + 9)]
    -- Now we have n = 9, we can use this to verify the original equation.
    simp_all
  
  have h₄ : (9 - 1) * 9 * (9 + 1) = 720 := by
    subst h₃
    norm_num
    <;> linarith
  
  have h₅ : n + 1 = 10 := by
    -- Since we have already established that n = 9, we can directly conclude that n + 1 = 10.
    linarith
  
  -- Use the given values and assumptions to simplify and conclude the proof.
  simp_all
  <;> linarith