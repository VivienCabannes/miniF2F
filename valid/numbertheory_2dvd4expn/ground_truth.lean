import Mathlib

open BigOperators Real Nat Topology Rat

theorem numbertheory_2dvd4expn (n : ℕ) (h₀ : n ≠ 0) : 2 ∣ 4 ^ n := by
  exact dvd_pow ⟨2, rfl⟩ h₀
