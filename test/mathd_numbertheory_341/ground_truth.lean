import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_341
  (a b c : ℕ)
  (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
  (h₁ : Nat.digits 10 ((5^100) % 1000) = [c,b,a]) :
  a + b + c = 13 := by
  have h₂ : 5 ^ 100 % 1000 = 625 := by
    norm_num [Nat.pow_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.lt_of_le_of_lt (Nat.zero_le _) (by norm_num : 1000 < 5 ^ 10)]
    <;> rfl
  
  have h₃ : Nat.digits 10 (5 ^ 100 % 1000) = [5, 2, 6] := by
    rw [h₂]
    <;> norm_num [Nat.digits_zero, Nat.div_eq_of_lt]
    <;> rfl
  
  have h₄ : [c, b, a] = [5, 2, 6] := by
    rw [h₃] at h₁
    rw [← h₁]
    <;> simp [h₂]
    <;> aesop
  
  have h₅ : a = 6 := by
    simp [List.cons, List.append, List.mem_cons, List.mem_singleton] at h₄
    <;> omega
  
  have h₆ : b = 2 := by
    simp [List.cons, List.append, List.mem_cons, List.mem_singleton] at h₄
    <;> omega
  
  have h₇ : c = 5 := by
    simp [List.cons, List.append, List.mem_cons, List.mem_singleton] at h₄
    <;> omega
  
  have h₈ : a + b + c = 13 := by
    subst_vars
    <;> norm_num
  
  apply h₈