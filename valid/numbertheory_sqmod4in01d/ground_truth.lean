import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_sqmod4in01d (a : ℤ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have case0 : a % 4 = 0 → a ^ 2 % 4 = 0 := by
    intro h
    -- Express a in the form of 4k, where k is an integer.
    have h2 : a ^ 2 % 4 = 0 := by
      -- Use the fact that a % 4 = 0 to simplify the expression.
      simp [h, pow_two, Int.mul_emod, Int.add_emod]
    -- The result follows directly from the simplified expression.
    exact h2
  
  have case1 : a % 4 = 1 → a ^ 2 % 4 = 1 := by
    -- Introduce the assumption that `a % 4 = 1`
    intro h
    -- Consider the cases for `a % 4` based on the assumption `h`
    have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
    -- Case analysis on the possible values of `a % 4`
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [h2, pow_two, Int.mul_emod, Int.add_emod, Int.emod_emod]
    -- For each case, simplify the expressions and check the result modulo 4
    <;> omega
    -- Use `omega` to solve the resulting equations
    <;> omega
    <;> omega
    <;> omega
  
  have case2 : a % 4 = 2 → a ^ 2 % 4 = 0 := by
    intro h
    have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [h1, pow_two, Int.mul_emod, Int.add_emod, Int.emod_emod]
    <;> omega
  
  have case3 : a % 4 = 3 → a ^ 2 % 4 = 1 := by
    intro h3
    -- We use the fact that a % 4 = 3 to simplify the expression for a^2 % 4
    simp [h3, pow_two, Int.mul_emod, Int.add_emod, Int.emod_emod]
    -- The simplification shows that a^2 % 4 = 1 when a % 4 = 3
    <;> norm_num
    <;> linarith
  
  have result : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
    /-
    To prove that for any integer \( a \), \( a^2 \mod 4 \) is either 0 or 1, we consider the possible values of \( a \mod 4 \). There are four cases to consider based on the remainder when \( a \) is divided by 4: 0, 1, 2, and 3.
    
    1. **Case 1: \( a \equiv 0 \mod 4 \)**
       - If \( a \equiv 0 \mod 4 \), then \( a = 4k \) for some integer \( k \).
       - Squaring \( a \): \( a^2 = (4k)^2 = 16k^2 \).
       - Taking modulo 4: \( 16k^2 \mod 4 = 0 \).
       - Therefore, \( a^2 \equiv 0 \mod 4 \).
    
    2. **Case 2: \( a \equiv 1 \mod 4 \)**
       - If \( a \equiv 1 \mod 4 \), then \( a = 4k + 1 \) for some integer \( k \).
       - Squaring \( a \): \( a^2 = (4k + 1)^2 = 16k^2 + 8k + 1 \).
       - Taking modulo 4: \( 16k^2 + 8k + 1 \mod 4 = 0 + 0 + 1 = 1 \).
       - Therefore, \( a^2 \equiv 1 \mod 4 \).
    
    3. **Case 3: \( a \equiv 2 \mod 4 \)**
       - If \( a \equiv 2 \mod 4 \), then \( a = 4k + 2 \) for some integer \( k \).
       - Squaring \( a \): \( a^2 = (4k + 2)^2 = 16k^2 + 16k + 4 \).
       - Taking modulo 4: \( 16k^2 + 16k + 4 \mod 4 = 0 + 0 + 0 = 0 \).
       - Therefore, \( a^2 \equiv 0 \mod 4 \).
    
    4. **Case 4: \( a \equiv 3 \mod 4 \)**
       - If \( a \equiv 3 \mod 4 \), then \( a = 4k + 3 \) for some integer \( k \).
       - Squaring \( a \): \( a^2 = (4k + 3)^2 = 16k^2 + 24k + 9 \).
       - Taking modulo 4: \( 16k^2 + 24k + 9 \mod 4 = 0 + 0 + 1 = 1 \).
       - Therefore, \( a^2 \equiv 1 \mod 4 \).
    
    From all four cases, we conclude that \( a^2 \mod 4 \) is either 0 or 1 for any integer \( a \).
    -/
    have : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      have : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
      rcases this with (h | h | h | h) <;> simp [h, pow_two, Int.mul_emod, Int.add_emod]
      <;> omega
    exact this
  
  match result with
  | Or.inl h =>
    -- If a^2 % 4 = 0, then the result is trivially true.
    exact Or.inl h
  | Or.inr h =>
    -- If a^2 % 4 = 1, then the result is also trivially true.
    exact Or.inr h