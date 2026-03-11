import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_1124
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 18∣374 * 10 + n) :
  n = 4 := by
  have h₂ : n = 4 := by
    -- We know that n is between 0 and 9, so we can check each case individually.
    have h₃ : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
      omega
    
    -- We will now consider each possible value of n and check if 18 divides 3740 + n.
    rcases h₃ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    <;> norm_num at h₁ ⊢
    <;>
    (try omega) <;>
    (try
      {
        -- For each case, we use the fact that 18 divides 3740 + n to derive a contradiction or confirm n = 4.
        norm_num at h₁
        <;>
        omega
      }) <;>
    (try
      {
        -- For the case n = 4, we confirm that 18 divides 3740 + 4 = 3744.
        omega
      })
    <;>
    (try
      {
        -- For other cases, we derive a contradiction.
        omega
      })
  
  exact h₂