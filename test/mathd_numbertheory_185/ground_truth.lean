import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_185
  (n : ℕ)
  (h₀ : n % 5 = 3) :
  (2 * n) % 5 = 1 := by
  have h₁ : (2 * n) % 5 = (2 * (n % 5)) % 5 := by
    rw [← Nat.mod_add_div n 5]
    simp [Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_self, zero_add, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
    <;> ring_nf at *
    <;> norm_num at *
    <;> simp [h₀, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_self, zero_add, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
    <;> omega
  
  have h₂ : (2 * n) % 5 = (2 * 3) % 5 := by
    rw [h₁]
    <;> rw [h₀]
    <;> norm_num
    <;> rfl
  
  have h₃ : (2 * n) % 5 = 1 := by
    rw [h₂]
    <;> norm_num
    <;> rfl
  
  rw [h₃]
  <;> norm_num