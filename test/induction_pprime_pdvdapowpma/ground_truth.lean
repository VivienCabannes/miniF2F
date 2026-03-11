import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem induction_pprime_pdvdapowpma
  (p a : ℕ)
  (h₀ : 0 < a)
  (h₁ : Nat.Prime p) :
  p ∣ (a^p - a) := by
  have h₂ : a ≤ a ^ p := by
    have h₃ : p ≠ 0 := Nat.Prime.ne_zero h₁
    have h₄ : a ≠ 0 := by linarith
    have h₅ : a ≤ a ^ p := by
      apply Nat.le_self_pow
      <;> omega
    exact h₅
  
  have h₃ : (a : ZMod p) ^ p = a := by
    haveI : Fact p.Prime := ⟨h₁⟩
    have h₄ : (a : ZMod p) ^ p = a := by
      rw [ZMod.pow_card]
    exact h₄
  
  have h₄ : p ∣ a ^ p - a := by
    haveI : Fact p.Prime := ⟨h₁⟩
    have h₅ : (p : ℕ) ∣ a ^ p - a := by
      have h₆ : (a ^ p : ZMod p) = a := by
        simpa [ZMod.nat_cast_self] using h₃
      have h₇ : (p : ℕ) ∣ a ^ p - a := by
        rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd]
        simp_all [ZMod.nat_cast_self, pow_succ, mul_comm]
        <;>
        ring_nf at *
        <;>
        simp_all [ZMod.nat_cast_zmod_eq_zero_iff_dvd, pow_succ, mul_comm]
      exact h₇
    exact h₅
  
  exact h₄