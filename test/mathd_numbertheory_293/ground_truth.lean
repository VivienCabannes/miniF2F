import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_293
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 11∣20 * 100 + 10 * n + 7) :
  n = 5 := by
  have h₂ : n = 5 := by
    -- Simplify the hypothesis h₁ to use modular arithmetic
    have h₃ : n ≤ 9 := h₀
    have h₄ : 11 ∣ 20 * 100 + 10 * n + 7 := h₁
    -- Use the fact that n is a digit to check all possible values
    interval_cases n <;> norm_num at h₄ ⊢
    <;>
    (try omega) <;>
    (try
      {
        norm_num at h₄
        <;>
        omega
      })
    <;>
    (try
      {
        rcases h₄ with ⟨k, hk⟩
        omega
      })
    <;>
    (try
      {
        omega
      })
  exact h₂