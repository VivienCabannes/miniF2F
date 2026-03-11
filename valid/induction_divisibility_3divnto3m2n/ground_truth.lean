import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_divisibility_3divnto3m2n (n : ℕ) : 3 ∣ n ^ 3 + 2 * n := by
  have base_case : 3 ∣ 0 ^ 3 + 2 * 0 := by
    -- Simplify the expression using basic arithmetic and divisibility rules.
    norm_num
    <;> decide
    <;> simp_all [Nat.mul_mod, Nat.pow_succ]
    <;> norm_num
    <;> decide
    <;> omega
  
  have inductive_step : ∀ k, 3 ∣ k ^ 3 + 2 * k → 3 ∣ (k + 1) ^ 3 + 2 * (k + 1) := by
    intro k hk
    have h1 : (k + 1) ^ 3 + 2 * (k + 1) = k ^ 3 + 2 * k + 3 * (k ^ 2 + k + 1) := by
      ring
    rw [h1]
    apply Nat.dvd_add
    · exact hk
    · simp [Nat.dvd_mul_right]
  
  have conclusion : 3 ∣ n ^ 3 + 2 * n := by
    -- Use the principle of mathematical induction to prove the statement for all natural numbers.
    induction n with
    | zero =>
      -- Base case: when n = 0, the expression simplifies to 0, which is divisible by 3.
      simpa using base_case
    | succ n ihn =>
      -- Inductive step: assume the statement holds for n, and prove it for n+1.
      simpa [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_zero] using
        inductive_step n (by simpa [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_zero] using ihn)
  
  -- Use the base case and inductive step to conclude the proof.
  simp_all [Nat.dvd_iff_mod_eq_zero]
  -- Simplify the expressions and apply modular arithmetic to show divisibility by 3.
  <;> ring_nf
  <;> omega