import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1964_p1_1 (n : ℕ) (h₀ : 7 ∣ 2 ^ n - 1) : 3 ∣ n := by
  have h₁ : 2 ^ n ≡ 1 [ZMOD 7] := by
    -- Use the definition of congruence modulo 7 to rewrite the hypothesis
    rw [Int.ModEq]
    -- Convert the hypothesis from divisibility form to congruence form
    rw [← Int.coe_nat_dvd] at h₀
    -- Normalize the numbers to simplify the expression
    norm_num at h₀ ⊢
    -- Use the omega tactic to solve the linear congruence problem
    omega
  
  have h₂ : orderOf (2 : ZMod 7) = 3 := by
    -- Establish that the order of 2 modulo 7 is 3.
    have h₂ : orderOf (2 : ZMod 7) = 3 := by
      -- Use the fact that 2^3 ≡ 1 [ZMOD 7] to confirm the order.
      rw [orderOf_eq_iff] <;> decide
    -- Conclude the proof by using the established order.
    simpa using h₂
  
  have h₃ : 3 ∣ n := by
    rw [Int.ModEq] at h₁
    norm_cast at h₁
    rw [Nat.dvd_iff_mod_eq_zero]
    -- We need to show that n % 3 = 0.
    have h₃ := h₁
    rw [← Nat.mod_add_div n 3] at h₃
    -- Express n as 3 * (n / 3) + (n % 3).
    simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod] at h₃
    -- Simplify the expression using properties of powers and modular arithmetic.
    have h₄ : n % 3 = 0 := by
      have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      -- Consider the possible values of n % 3.
      rcases this with (h | h | h) <;> simp [h, h₂, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod] at h₃
      -- Case analysis on the possible values of n % 3.
      <;> omega
    -- Conclude that n % 3 must be 0.
    exact h₄
  
  rw [← Nat.mod_add_div n 3]
  simp_all [Int.ModEq, Nat.ModEq]
  <;> omega