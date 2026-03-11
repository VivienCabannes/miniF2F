import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_sqmod3in01d (a : ℤ) : a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by
  have case1 : a % 3 = 0 → a ^ 2 % 3 = 0 := by
    intro h
    -- Simplify the expression using the given condition `h` and properties of modular arithmetic.
    simp [h, pow_two, Int.mul_emod]
    -- `h` states that `a % 3 = 0`, which means `a` is divisible by 3.
    -- `pow_two` states that `a^2 = a * a`.
    -- `Int.mul_emod` states that `(a * a) % 3 = (a % 3 * a % 3) % 3`.
    -- Since `a % 3 = 0`, the expression simplifies to `0 * 0 % 3 = 0`.
    <;> simp [h]
    -- Further simplification to ensure the proof is complete.
    <;> simp [h]
    <;> simp [h]
  
  have case2 : a % 3 = 1 → a ^ 2 % 3 = 1 := by
    intro h
    have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1) <;> simp [h1, pow_two, Int.mul_emod, Int.add_emod, Int.emod_emod] at case1 ⊢ <;> omega
  
  have case3 : a % 3 = 2 → a ^ 2 % 3 = 1 := by
    intro h
    simp_all [pow_two, Int.mul_emod, Int.add_emod]
    -- Simplify the expression using modular arithmetic properties
    <;> omega
  
  have all_cases_covered : ∀ n : ℤ, n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    -- We use the `exact` tactic to directly apply the given cases to any integer `n`.
    intro n
    omega
  
  have final_proof : a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by
    have h₀ : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := all_cases_covered a
    rcases h₀ with (h₀ | h₀ | h₀) <;> simp [h₀, pow_two, Int.mul_emod, Int.add_emod, Int.emod_emod]
    <;> norm_num <;> aesop
    <;> norm_num <;> aesop
    <;> norm_num <;> aesop
  
  -- We use the given cases to construct a proof for the final statement.
  match all_cases_covered a with
  | Or.inl h =>
    -- Case 1: a ≡ 0 (mod 3)
    -- We apply the given case1 to conclude a^2 ≡ 0 (mod 3)
    exact Or.inl (case1 h)
  | Or.inr (Or.inl h) =>
    -- Case 2: a ≡ 1 (mod 3)
    -- We apply the given case2 to conclude a^2 ≡ 1 (mod 3)
    exact Or.inr (case2 h)
  | Or.inr (Or.inr h) =>
    -- Case 3: a ≡ 2 (mod 3)
    -- We apply the given case3 to conclude a^2 ≡ 1 (mod 3)
    exact Or.inr (case3 h)