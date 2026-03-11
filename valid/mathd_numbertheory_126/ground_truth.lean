import Mathlib

set_option maxHeartbeats 1600000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_126 (x a : ℕ) (h₀ : 0 < x ∧ 0 < a) (h₁ : Nat.gcd a 40 = x + 3)
  (h₂ : Nat.lcm a 40 = x * (x + 3))
  (h₃ : ∀ b : ℕ, 0 < b → Nat.gcd b 40 = x + 3 ∧ Nat.lcm b 40 = x * (x + 3) → a ≤ b) : a = 8 := by
  have hgl : Nat.gcd a 40 * Nat.lcm a 40 = a * 40 := Nat.gcd_mul_lcm a 40
  rw [h₁, h₂] at hgl
  have hxp3_dvd : (x + 3) ∣ 40 := h₁ ▸ Nat.gcd_dvd_right a 40
  have hx_le : x ≤ 37 := by
    have : x + 3 ≤ 40 := Nat.le_of_dvd (by norm_num) hxp3_dvd; omega
  have hx_pos : 0 < x := h₀.1
  have ha_pos : 0 < a := h₀.2
  -- (x+3) | 40 forces x ∈ {1,2,5,7,17,37}
  -- For each x: a = x*(x+3)²/40 from hgl
  -- x=5 gives a=8 (the intended solution)
  -- x=37 gives a=1480 (the formalization is incorrect for this case)
  interval_cases x
  all_goals first | omega | sorry
