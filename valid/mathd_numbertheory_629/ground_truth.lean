import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_629 : IsLeast { t : ℕ | 0 < t ∧ Nat.lcm 12 t ^ 3 = (12 * t) ^ 2 } 18 := by
  have h1 : 0 < 18 ∧ Nat.lcm 12 18 ^ 3 = (12 * 18) ^ 2 := by
    constructor
    -- Prove that 0 < 18
    norm_num
    -- Simplify the expression using the property of the least common multiple (LCM)
    simp [Nat.lcm, Nat.gcd_eq_gcd_ab 12 18]
    -- Normalize the numbers to show the equality
    <;> norm_num
    <;> ring
    <;> norm_num
    <;> ring
  
  have h2 : ∀ t : ℕ, 0 < t ∧ Nat.lcm 12 t ^ 3 = (12 * t) ^ 2 → 18 ≤ t := by
    intro t ht
    -- We start by assuming the given condition for t.
    have h2 := ht.2
    -- We simplify the equation using properties of the least common multiple (lcm).
    simp [Nat.lcm] at h2
    -- We use contradiction to show that t must be at least 18.
    contrapose! h2
    -- We use interval_cases to check each possible value of t and verify the equation.
    interval_cases t <;> simp_all
    -- We use norm_num to simplify numerical expressions.
    <;> norm_num
    -- We use linarith to handle the arithmetic and inequalities.
    <;> linarith
  
  refine' ⟨by simpa [Nat.lcm] using h1.2, fun a h => _⟩
  -- Verify that 18 satisfies the condition
  have h1' : 0 < 18 ∧ Nat.lcm 12 18 ^ 3 = (12 * 18) ^ 2 := by simpa [Nat.lcm] using h1
  have h2' : ∀ t : ℕ, 0 < t ∧ Nat.lcm 12 t ^ 3 = (12 * t) ^ 2 → 18 ≤ t := by simpa [Nat.lcm] using h2
  -- Use the given conditions to show that any other solution must be at least 18
  exact h2' a ⟨h.1, h.2⟩