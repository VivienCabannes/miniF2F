import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_11div10tonmn1ton
  (n : ℕ) :
  11 ∣ (10^n - (-1 : ℤ)^n) := by
  have h_main : (11 : ℤ) ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
    have h₁ : (10 : ℤ) ≡ (-1 : ℤ) [ZMOD 11] := by
      -- Prove that 10 ≡ -1 mod 11
      norm_num [Int.ModEq]
    -- Raise both sides to the power of n
    have h₂ : (10 : ℤ) ^ n ≡ (-1 : ℤ) ^ n [ZMOD 11] := by
      -- Use the property of congruences that if a ≡ b mod m, then a^n ≡ b^n mod m
      calc
        (10 : ℤ) ^ n ≡ (-1 : ℤ) ^ n [ZMOD 11] := by
          -- Apply the power rule to the congruence
          simpa using h₁.pow n
        _ ≡ (-1 : ℤ) ^ n [ZMOD 11] := by rfl
    -- Convert the congruence back to divisibility
    have h₃ : (11 : ℤ) ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
      -- Use the definition of congruence to get the divisibility condition
      rw [Int.ModEq] at h₂
      -- Simplify the expression to show the divisibility
      simpa [Int.emod_eq_emod_iff_emod_sub_eq_zero] using h₂
    -- The final result follows from the previous steps
    exact h₃
  
  have h_final : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
    simpa [Int.emod_eq_emod_iff_emod_sub_eq_zero] using h_main
  
  exact h_final