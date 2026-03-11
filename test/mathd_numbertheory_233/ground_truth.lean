import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_233
  (b :  ZMod (11^2))
  (h₀ : b = 24⁻¹) :
  b = 116 := by
  have h₁ : (24 : ZMod (11 ^ 2)) * 116 = 1 := by
    norm_num [ZMod.val_mul, ZMod.val_nat_cast, ZMod.val_one, pow_succ]
    <;> rfl
  
  have h₂ : (24 : ZMod (11 ^ 2))⁻¹ = 116 := by
    apply Eq.symm
    apply Eq.symm
    rw [← mul_one (116 : ZMod (11 ^ 2)), ← h₁]
    simp [mul_assoc, mul_comm, mul_left_comm, inv_mul_cancel_left]
    <;> norm_num
    <;> rfl
  
  have h₃ : b = 116 := by
    rw [h₀, h₂]
    <;> rfl
  
  exact h₃