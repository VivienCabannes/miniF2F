import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1964_p1_2 (n : ℕ) : ¬7 ∣ 2 ^ n + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  -- We need to show that 2^n + 1 % 7 ≠ 0 for any natural number n.
  have h : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
    -- We observe that the powers of 2 modulo 7 cycle every 3 exponents: 2, 4, 1.
    induction n with
    | zero => simp
    | succ n ih =>
      -- Using the fact that 2^(n+1) % 7 depends on 2^n % 7.
      cases ih with
      | inl h =>
        rw [Nat.pow_succ]
        norm_num [h, Nat.mul_mod, Nat.add_mod]
      | inr h =>
        cases h with
        | inl h =>
          rw [Nat.pow_succ]
          norm_num [h, Nat.mul_mod, Nat.add_mod]
        | inr h =>
          rw [Nat.pow_succ]
          norm_num [h, Nat.mul_mod, Nat.add_mod]
  -- Since 2^n % 7 cycles through 2, 4, 1, adding 1 to each case gives 3, 5, 2, none of which are 0 modulo 7.
  rcases h with (h | h | h) <;> simp [h, Nat.add_mod, Nat.mul_mod]