import Mathlib
import Aesop
set_option maxHeartbeats 400000
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_780 (m x : ℤ) (h₀ : 10 ≤ m) (h₁ : m ≤ 99) (h₂ : (6 * x) % m = 1) (h₃ : (x - 6 ^ 2) % m = 0) : m = 43 := by
  interval_cases m <;> simp_all (config := {decide := true})
  all_goals
    have h₄ := h₃
    have h₅ := h₂
    omega
