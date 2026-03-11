import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_12 :
  Finset.card (Finset.filter (λ x => 20∣x) (Finset.Icc 15 85)) = 4 := by
  have h_main : Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85) = {20, 40, 60, 80} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · -- Prove the forward direction: if x is in the filter, then x is one of the specified numbers.
      intro h
      have h₁ : 15 ≤ x ∧ x ≤ 85 := by tauto
      have h₂ : 20 ∣ x := by tauto
      have h₃ : x = 20 ∨ x = 40 ∨ x = 60 ∨ x = 80 := by
        -- We know x is between 15 and 85 and divisible by 20.
        -- So, x can be 20, 40, 60, or 80.
        have h₄ : x ≤ 85 := by linarith
        have h₅ : 15 ≤ x := by linarith
        have h₆ : 20 ∣ x := by tauto
        -- We need to show x is one of the specified numbers.
        have h₇ : x = 20 ∨ x = 40 ∨ x = 60 ∨ x = 80 := by
          -- Since 20 divides x, x is a multiple of 20.
          -- The multiples of 20 between 15 and 85 are 20, 40, 60, and 80.
          have h₈ : x % 20 = 0 := by
            omega
          have h₉ : x ≤ 85 := by linarith
          have h₁₀ : 15 ≤ x := by linarith
          have h₁₁ : x = 20 ∨ x = 40 ∨ x = 60 ∨ x = 80 := by
            omega
          exact h₁₁
        exact h₇
      -- Now we know x is one of the specified numbers.
      tauto
    · -- Prove the reverse direction: if x is one of the specified numbers, then x is in the filter.
      intro h
      have h₁ : x = 20 ∨ x = 40 ∨ x = 60 ∨ x = 80 := by tauto
      have h₂ : 15 ≤ x ∧ x ≤ 85 ∧ 20 ∣ x := by
        rcases h₁ with (rfl | rfl | rfl | rfl)
        · -- Case x = 20
          norm_num
        · -- Case x = 40
          norm_num
        · -- Case x = 60
          norm_num
        · -- Case x = 80
          norm_num
      tauto
  
  have h_card : Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
    rw [h_main]
    <;> norm_num
    <;> decide
  
  apply h_card