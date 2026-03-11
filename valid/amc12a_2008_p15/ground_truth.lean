import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2008_p15 (k : ℕ) (h₀ : k = 2008 ^ 2 + 2 ^ 2008) : (k ^ 2 + 2 ^ k) % 10 = 6 := by
  have h₁ : (2008 ^ 2) % 10 = 4 := by
    have h₁ : 2008 ^ 2 % 10 = 4 := by
      -- Calculate 2008 modulo 10, which is 8.
      have h₂ : 2008 % 10 = 8 := by norm_num
      -- Calculate 8 squared modulo 10, which is 4.
      have h₃ : 8 ^ 2 % 10 = 4 := by norm_num
      -- Combine the results to conclude the proof.
      norm_num [h₂, h₃]
    have h₂ : 2 ^ 2008 % 10 = 6 := by
      -- Recognize the pattern in powers of 2 modulo 10.
      have h₃ : 2 ^ 4 % 10 = 6 := by norm_num
      -- Use the pattern to find 2^2008 modulo 10.
      have h₄ : 2008 % 4 = 0 := by norm_num
      norm_num [h₃, h₄, pow_mul]
    -- Combine the results to find the final answer.
    norm_num [h₀, h₁, h₂]
  
  have h₂ : (2 ^ 2008) % 10 = 6 := by
    -- Recognize that 2008 ends in 4, and 2008^2 = 2008 * 2008, so 4 * 4 = 16, which leaves a digit 6.
    have h₂ : (2 ^ 2008) % 10 = 6 := by
      -- Use the pattern in the powers of 2 modulo 10 to find the remainder.
      -- The pattern repeats every 4: 2, 4, 8, 6.
      -- 2008 is divisible by 4, so 2^2008 ≡ 6 (mod 10).
      have h₃ : (2 ^ 4) % 10 = 6 := by norm_num
      have h₄ : 2008 % 4 = 0 := by norm_num
      have h₅ : (2 ^ 2008) % 10 = (2 ^ (4 * (2008 / 4))) % 10 := by norm_num
      rw [pow_mul] at h₅
      simp [h₃, h₄] at h₅
      -- Using the above steps, we conclude that 2^2008 % 10 = 6.
      <;> norm_num at h₅
      <;> assumption
    -- Using the derived result, we conclude that k % 10 = 4.
    simp [h₂, h₀]
    <;> norm_num
    <;> omega
  
  have h₃ : k % 10 = (4 + 6) % 10 := by
    rw [h₀]
    simp [h₁, h₂, Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.add_mod, Nat.mul_mod]
  
  have h₄ : k % 10 = 0 := by
    simp_all [Nat.pow_mod, Nat.add_mod, Nat.mul_mod]
    -- Simplify the expressions modulo 10 using the properties of powers and modular arithmetic.
    -- This step uses the fact that 2008^2 % 10 = 4 and 2^2008 % 10 = 6, leading to k % 10 = (4 + 6) % 10.
    <;> norm_num
    -- Normalize the numerical expression to confirm that (4 + 6) % 10 = 0, implying k % 10 = 0.
    <;> rfl
  
  have h₅ : (k ^ 2) % 10 = 0 := by
    norm_num [h₀, h₁, h₂, h₃, h₄, Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    <;> decide
    <;> rfl
    <;> decide
    <;> rfl
  
  have h₆ : (2 ^ k) % 10 = 6 := by
    have h₆ : k % 10 = 0 := by omega
    have h₇ : (k ^ 2) % 10 = 0 := by omega
    have h₈ : (2 ^ k) % 10 = 6 := by
      -- We use the fact that the pattern of 2^n modulo 10 repeats every 4 exponents: 2, 4, 8, 6
      -- Since k is even and ends with 0, we can express k as 4m for some integer m
      -- Therefore, 2^k = 2^(4m) = (2^4)^m = 76^m ≡ 6 (mod 10)
      have h₈ : ∀ n : ℕ, n ≥ 1 → (2 ^ (4 * n)) % 10 = 6 := by
        intro n hn
        induction' hn with n hn
        · norm_num -- Base case: when n = 1, 2^(4*1) = 2^4 = 16 ≡ 6 (mod 10)
        · simp_all [Nat.mul_succ, pow_add, pow_one, Nat.mul_mod, Nat.pow_mod, Nat.add_mod]
          -- Inductive step: assume 2^(4n) ≡ 6 (mod 10), then 2^(4(n+1)) = 2^(4n + 4) = (2^4)^n * 2^4 = 16^n * 16 ≡ 6 * 6 ≡ 6 (mod 10)
      have h₉ : k % 4 = 0 := by omega
      have h₁₀ : k = 4 * (k / 4) := by omega
      rw [h₁₀]
      apply h₈
      omega
    exact h₈
  
  have h₇ : (k ^ 2 + 2 ^ k) % 10 = (0 + 6) % 10 := by
    simp [h₁, h₂, h₃, h₄, h₅, h₆, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
    <;> norm_num
    <;> aesop
  
  have h₈ : (k ^ 2 + 2 ^ k) % 10 = 6 := by
    -- We use the properties of modular arithmetic and the given conditions to simplify the problem.
    have h₁ : (2008 ^ 2) % 10 = 4 := h₁
    have h₂ : (2 ^ 2008) % 10 = 6 := h₂
    have h₃ : k % 10 = (4 + 6) % 10 := h₃
    have h₄ : k % 10 = 0 := h₄
    have h₅ : (k ^ 2) % 10 = 0 := h₅
    have h₆ : (2 ^ k) % 10 = 6 := h₆
    have h₇ : (k ^ 2 + 2 ^ k) % 10 = (0 + 6) % 10 := h₇
    -- Using the properties of modular arithmetic, we can conclude that the units digit of k^2 + 2^k is 6.
    omega
  
  apply h₈