import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_prmdvsneqnsqmodpeq0 (n : ℤ) (p : ℕ) (h₀ : Nat.Prime p) :
  ↑p ∣ n ↔ n ^ 2 % p = 0 := by
  have forward : ↑p ∣ n → n ^ 2 % p = 0 := by
    intro h
    -- Given that p divides n, we can write n as p * k for some integer k.
    cases' h with k hk
    -- Substitute n = p * k into n^2 and simplify.
    rw [hk, pow_two]
    -- Simplify the expression modulo p.
    simp [Int.mul_emod, Int.add_emod, Int.emod_emod]
    -- Since p^2 % p = 0, the entire expression is divisible by p.
    <;> simp [h₀.ne_zero]
    -- Therefore, n^2 % p = 0.
    <;> simp [h₀.ne_zero]
    <;> simp [h₀.ne_zero]
  
  have backward : n ^ 2 % p = 0 → ↑p ∣ n := by
    intro h₁
    have h₂ : ↑p ∣ n ^ 2 := by
      -- If n^2 % p = 0, then p divides n^2.
      rw [Int.dvd_iff_emod_eq_zero]
      exact h₁
    -- Since p is prime, if p divides n^2, then p divides n.
    exact (Nat.prime_iff_prime_int.mp h₀).dvd_of_dvd_pow h₂
  
  apply Iff.intro
  -- Forward direction: If p divides n, then n^2 % p = 0
  intro h
  apply forward
  assumption
  -- Backward direction: If n^2 % p = 0, then p divides n
  intro h
  apply backward
  assumption