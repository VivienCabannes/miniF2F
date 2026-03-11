import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12_2001_p2 (a b n : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9) (h₂ : n = 10 * a + b)
  (h₃ : n = a * b + a + b) : b = 9 := by
  have eq1 : 10 * a + b = a * b + a + b := by
    -- Simplify the given equation using the two expressions for n
    simp_all only [h₂, h₃, add_comm]
    -- Use linear arithmetic to confirm the equality
    <;> omega
  
  have eq2 : 10 * a = a * b + a := by
    -- We start by assuming the given equality and simplifying it.
    have h₄ : 10 * a = a * b + a := by
      -- We know that n = 10a + b and n = ab + a + b.
      -- By equating the two expressions for n, we get:
      -- 10a + b = ab + a + b.
      -- Subtracting b from both sides, we obtain:
      -- 10a = ab + a.
      linarith
    -- Simplify the context by substituting the known values.
    simp_all
  
  have eq3 : 10 * a = a * (b + 1) := by
    -- Simplify the given equations using the definitions of n
    simp_all only [Nat.mul_add, Nat.add_assoc, Nat.add_right_comm, Nat.add_comm]
    -- Use linear arithmetic to conclude the proof
    nlinarith
  
  have eq4 : 10 = b + 1 := by
    have h₄ : b + 1 ≤ 10 := by
      -- Since a is non-zero and positive, b + 1 must be less than or equal to 10.
      nlinarith
    have h₅ : b ≤ 9 := by
      -- Given the constraints on a and b, b must be less than or equal to 9.
      nlinarith
    have h₆ : b + 1 ≥ 10 := by
      -- From the equation 10a = a(b + 1), we derive that b + 1 must be at least 10.
      nlinarith
    -- Combining the inequalities, we conclude that b + 1 must be exactly 10.
    linarith
  
  have eq5 : b = 9 := by
    -- From the equation 10 = b + 1, solve for b.
    have h₅ : b = 9 := by
      linarith
    -- The result is b = 9.
    exact h₅
  
  -- We have already shown that b must be 9, so we can directly use this result.
  simpa using eq5