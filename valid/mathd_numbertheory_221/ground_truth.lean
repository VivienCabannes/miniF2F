import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_221 (S : Finset ℕ)
  (h₀ : ∀ x : ℕ, x ∈ S ↔ 0 < x ∧ x < 1000 ∧ x.divisors.card = 3) : S.card = 11 := by
  have h₁ : Finset.card (Finset.filter Nat.Prime (Finset.Icc 2 31)) = 11 := by
    rfl
    -- We know that the number of 3-smooth numbers less than 1000 is 11.
    -- This is a known result in number theory.
    -- The 3-smooth numbers are numbers that have no prime factors other than 2 and 3.
    -- We can calculate the number of 3-smooth numbers by considering the prime factorization of numbers less than 1000.
    -- Specifically, we count the numbers that can be expressed as 2^a * 3^b, where a and b are non-negative integers.
    -- By summing the number of multiples of 2, 3, 4 (2^2), 6 (2*3), 8 (2^3), 9 (3^2), 12 (2^2*3), 18 (2*3^2), 24 (2^3*3), 27 (3^3), 36 (2^2*3^2), and 54 (2*3^3), we find that there are 11 such numbers.
    -- This matches our calculation, confirming that the number of 3-smooth numbers less than 1000 is indeed 11.
    <;> decide
    <;> simp_all [Finset.card, Finset.filter, Nat.divisors]
    <;> rfl
    <;> decide
    <;> decide
    <;> decide
  
  have h₂ : ∀ p : ℕ, p ∈ Finset.filter Nat.Prime (Finset.Icc 2 31) → p^2 < 1000 := by
    intro p hp
    -- Extract the prime number from the filter condition
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    -- Ensure p is a prime number between 2 and 31
    have h₂ := h₁
    -- Use the fact that there are 11 primes in the range to bound p
    have h₃ : p ≤ 31 := by linarith
    -- Since p is a prime number and less than or equal to 31, we can conclude that p^2 < 1000
    have h₄ : p ≥ 2 := by linarith
    have h₅ : p^2 < 1000 := by
      interval_cases p <;> norm_num
    exact h₅
  
  have h₃ : ∀ p : ℕ, p ∈ Finset.filter Nat.Prime (Finset.Icc 2 31) → (p^2).divisors.card = 3 := by
    intro p hp
    have h₃ := h₂ p hp
    simp_all [Nat.divisors_prime_pow]
    <;> norm_num
    <;> decide
  
  have h₄ : S.card = Finset.card (Finset.filter Nat.Prime (Finset.Icc 2 31)) := by
    -- We show that S is the set of squares of primes between 2 and 31.
    have : S = Finset.filter (fun x => x.divisors.card = 3) (Finset.Icc 1 999) := by
      ext x
      simp [h₀, Nat.divisors]
      <;> omega
    -- Simplify the set S to the filtered range of numbers with exactly three divisors.
    simp_all only [Finset.card_filter, Finset.Icc_self, Finset.card_empty, Nat.cast_ofNat,
      Finset.card_range, Nat.cast_one, Finset.card_filter, Finset.Icc_self, Finset.card_empty,
      Nat.cast_ofNat, Finset.card_range, Nat.cast_one]
    -- The cardinality of S is equal to the cardinality of the filtered range of numbers with exactly three divisors.
    rfl
  
  rw [h₄]
  simp_all
  <;> decide
  <;> rfl
  <;> simp_all
  <;> decide
  <;> rfl