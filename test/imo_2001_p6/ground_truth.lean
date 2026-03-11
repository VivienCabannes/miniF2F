import Mathlib

open BigOperators Real Nat Topology Rat

theorem imo_2001_p6
  (a b c d : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : d < c)
  (h₂ : c < b)
  (h₃ : b < a)
  (h₄ : a * c + b * d = (b + d + a - c) * (b + d + c - a)) :
  ¬ Nat.Prime (a * b + c * d) := by
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  have hbdca : a < b + d + c := by
    by_contra hle; push_neg at hle
    have : b + d + c - a = 0 := Nat.sub_eq_zero_of_le hle
    rw [this, mul_zero] at h₄
    have : 0 < a * c + b * d := Nat.add_pos_left (Nat.mul_pos ha hc) _
    omega
  have h₄z : (a : ℤ) * c + b * d = (b + d + a - c) * (b + d + c - a) := by
    have h4' := h₄
    have hle1 : c ≤ b + d + a := by omega
    have hle2 : a ≤ b + d + c := by omega
    zify [hle1, hle2] at h4'
    linarith
  have key : (a : ℤ)^2 - a*c + c^2 = b^2 + b*d + d^2 := by
    nlinarith [sq_nonneg ((a : ℤ) - c), sq_nonneg ((b : ℤ) + d)]
  have identity_z : ((a : ℤ)*c + b*d) * (b^2 + b*d + d^2) = (a*b + c*d) * (a*d + b*c) := by
    linear_combination -(↑b) * (↑d) * key
  have identity_n : (a*c + b*d) * (b^2 + b*d + d^2) = (a*b + c*d) * (a*d + b*c) := by
    exact_mod_cast identity_z
  have ineq1_z : (a : ℤ)*c + b*d < a*b + c*d := by nlinarith
  have ineq1 : a*c + b*d < a*b + c*d := by exact_mod_cast ineq1_z
  have ineq2_z : (a : ℤ)*d + b*c < a*c + b*d := by nlinarith
  have ineq2 : a*d + b*c < a*c + b*d := by exact_mod_cast ineq2_z
  have pos_acbd : 0 < a*c + b*d := Nat.add_pos_left (Nat.mul_pos ha hc) _
  have S_lt : b^2 + b*d + d^2 < a*b + c*d := by
    have h1 : (a*b + c*d) * (a*d + b*c) < (a*b + c*d) * (a*c + b*d) :=
      Nat.mul_lt_mul_of_pos_left ineq2 (Nat.add_pos_left (Nat.mul_pos ha hb) _)
    have h2 : (a*c + b*d) * (b^2 + b*d + d^2) < (a*c + b*d) * (a*b + c*d) := by
      calc (a*c + b*d) * (b^2 + b*d + d^2)
          = (a*b + c*d) * (a*d + b*c) := identity_n
        _ < (a*b + c*d) * (a*c + b*d) := h1
        _ = (a*c + b*d) * (a*b + c*d) := Nat.mul_comm _ _
    exact (Nat.lt_of_mul_lt_mul_left h2)
  intro hprime
  have hdvd : (a*b + c*d) ∣ (a*c + b*d) * (b^2 + b*d + d^2) :=
    ⟨a*d + b*c, identity_n⟩
  rcases hprime.dvd_mul.mp hdvd with h_d1 | h_d2
  · exact absurd (Nat.le_of_dvd pos_acbd h_d1) (Nat.not_le.mpr ineq1)
  · have pos_S : 0 < b^2 + b*d + d^2 := by positivity
    exact absurd (Nat.le_of_dvd pos_S h_d2) (Nat.not_le.mpr S_lt)
