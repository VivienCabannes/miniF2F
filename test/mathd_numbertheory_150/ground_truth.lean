import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_150
  (n : ℕ)
  (h₀ : ¬ Nat.Prime (7 + 30 * n)) :
  6 ≤ n := by
  have h₁ : n ≥ 6 := by
    by_contra h
    -- Assume for contradiction that n < 6
    have h₂ : n ≤ 5 := by linarith
    -- Since n is a natural number, n < 6 implies n ≤ 5
    interval_cases n <;> norm_num [Nat.Prime] at h₀ ⊢ <;>
      (try contradiction) <;>
      (try norm_num) <;>
      (try decide) <;>
      (try omega)
    <;>
      norm_num [Nat.Prime] at h₀ ⊢ <;>
      (try contradiction) <;>
      (try norm_num) <;>
      (try decide) <;>
      (try omega)
  
  linarith