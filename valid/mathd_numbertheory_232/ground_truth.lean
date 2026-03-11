import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_232 (x y z : ZMod 31) (h₀ : x = 3⁻¹) (h₁ : y = 5⁻¹)
  (h₂ : z = (x + y)⁻¹) : z = 29 := by
  have h₃ : x = 21 := by
    rw [h₀] at *
    rfl
  
  have h₄ : y = 25 := by
    rw [h₃] at h₀ h₂
    norm_num [h₀, h₁, h₂]
    <;> rfl
  
  have h₅ : x + y = 15 := by
    -- Substitute the given values for x and y into the equation x + y
    simp_all [ZMod.nat_cast_self]
    -- Simplify the equation using the given values
    <;> norm_num
    -- Verify the numerical result
    <;> rfl
  
  have h₆ : z = 29 := by
    -- Substitute the given values of x, y, and x + y into the equation for z.
    rw [h₂, h₃, h₄] at *
    -- Simplify the equation using the given values and properties of modular arithmetic.
    norm_num [h₃, h₄, h₅, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    -- Verify that the computed value of z matches the expected result.
    <;> rfl
  
  simp_all
  <;> rfl
  <;> norm_num
  <;> rfl