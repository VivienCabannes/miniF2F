import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_289
  (k t m n : ℕ)
  (h₀ : Nat.Prime m ∧ Nat.Prime n)
  (h₁ : t < k)
  (h₂ : k^2 - m * k + n = 0)
  (h₃ : t^2 - m * t + n = 0) :
  m^n + n^m + k^t + t^k = 20 := by
  have h₄ : (m : ℤ) = (k : ℤ) + (t : ℤ) := by
    have h₄₁ : ((k : ℤ) - (t : ℤ)) * ((k : ℤ) + (t : ℤ) - (m : ℤ)) = 0 := by
      have h₄₂ : (k : ℤ) ^ 2 - m * k + n = 0 := by exact_mod_cast h₂
      have h₄₃ : (t : ℤ) ^ 2 - m * t + n = 0 := by exact_mod_cast h₃
      have h₄₄ : ((k : ℤ) ^ 2 - m * k + n) - ((t : ℤ) ^ 2 - m * t + n) = 0 := by
        linarith
      have h₄₅ : ((k : ℤ) ^ 2 - m * k + n) - ((t : ℤ) ^ 2 - m * t + n) = (k : ℤ) ^ 2 - m * k + n - ((t : ℤ) ^ 2 - m * t + n) := by ring
      rw [h₄₅] at h₄₄
      have h₄₆ : (k : ℤ) ^ 2 - m * k + n - ((t : ℤ) ^ 2 - m * t + n) = (k : ℤ) ^ 2 - m * k - (t : ℤ) ^ 2 + m * t := by ring
      rw [h₄₆] at h₄₄
      have h₄₇ : (k : ℤ) ^ 2 - m * k - (t : ℤ) ^ 2 + m * t = 0 := by linarith
      have h₄₈ : (k : ℤ) ^ 2 - (t : ℤ) ^ 2 - m * k + m * t = 0 := by linarith
      have h₄₉ : ((k : ℤ) - (t : ℤ)) * ((k : ℤ) + (t : ℤ)) - m * ((k : ℤ) - (t : ℤ)) = 0 := by
        ring_nf at h₄₈ ⊢
        <;> linarith
      have h₅₀ : ((k : ℤ) - (t : ℤ)) * ((k : ℤ) + (t : ℤ) - (m : ℤ)) = 0 := by
        ring_nf at h₄₉ ⊢
        <;> linarith
      exact h₅₀
    have h₅₁ : (k : ℤ) ≠ (t : ℤ) := by
      intro h
      have h₅₂ : k = t := by
        norm_cast at h
        <;> linarith
      have h₅₃ : t < k := h₁
      linarith
    have h₅₄ : ((k : ℤ) + (t : ℤ) - (m : ℤ)) = 0 := by
      have h₅₅ : ((k : ℤ) - (t : ℤ)) ≠ 0 := by
        intro h
        apply h₅₁
        linarith
      have h₅₆ : ((k : ℤ) - (t : ℤ)) * ((k : ℤ) + (t : ℤ) - (m : ℤ)) = 0 := h₄₁
      have h₅₇ : ((k : ℤ) + (t : ℤ) - (m : ℤ)) = 0 := by
        apply mul_left_cancel₀ h₅₅
        linarith
      exact h₅₇
    have h₅₈ : (m : ℤ) = (k : ℤ) + (t : ℤ) := by linarith
    exact_mod_cast h₅₈
  
  have h₅ : m = k + t := by
    have h₅₁ : (m : ℤ) = (k : ℤ) + (t : ℤ) := h₄
    have h₅₂ : m = k + t := by
      norm_cast at h₅₁ ⊢
      <;> linarith
    exact h₅₂
  
  have h₆ : n = t * k := by
    have h₆₁ : k ^ 2 + n = m * k := by
      have h₆₂ : (k ^ 2 : ℤ) + (n : ℤ) = (m * k : ℤ) := by
        have h₆₃ : (k ^ 2 : ℤ) - m * k + n = 0 := h₂
        linarith
      norm_cast at h₆₂ ⊢
      <;> linarith
    have h₆₄ : n = t * k := by
      have h₆₅ : m = k + t := h₅
      rw [h₆₅] at h₆₁
      ring_nf at h₆₁ ⊢
      <;> nlinarith [h₀.1.two_le, h₀.2.two_le, h₁, Nat.Prime.ne_zero h₀.1, Nat.Prime.ne_zero h₀.2,
        Nat.Prime.pos h₀.1, Nat.Prime.pos h₀.2]
    exact h₆₄
  
  have h₇ : t = 1 := by
    have h₇₁ : n = t * k := h₆
    have h₇₂ : Nat.Prime n := h₀.2
    have h₇₃ : t ∣ n := by
      use k
      <;> linarith
    have h₇₄ : t = 1 ∨ t = n := by
      have h₇₅ : Nat.Prime n := h₀.2
      exact h₇₅.eq_one_or_self_of_dvd _ h₇₃
    cases h₇₄ with
    | inl h₇₄ =>
      exact h₇₄
    | inr h₇₄ =>
      have h₇₅ : t = n := h₇₄
      have h₇₆ : t < k := h₁
      have h₇₇ : k > t := by linarith
      have h₇₈ : n = t * k := h₆
      have h₇₉ : t * k > t * t := by
        nlinarith [h₀.1.two_le, h₀.2.two_le]
      have h₈₀ : t > 0 := by
        nlinarith [h₀.1.two_le, h₀.2.two_le]
      have h₈₁ : t = n := by linarith
      have h₈₂ : k > t := by linarith
      have h₈₃ : n = t * k := h₆
      have h₈₄ : t * k > t * t := by
        nlinarith [h₀.1.two_le, h₀.2.two_le]
      have h₈₅ : t > 0 := by
        nlinarith [h₀.1.two_le, h₀.2.two_le]
      nlinarith [h₀.1.two_le, h₀.2.two_le]
  
  have h₈ : k = n := by
    have h₈₁ : n = t * k := h₆
    have h₈₂ : t = 1 := h₇
    rw [h₈₂] at h₈₁
    ring_nf at h₈₁ ⊢
    <;> nlinarith [h₀.1.two_le, h₀.2.two_le, h₁, Nat.Prime.ne_zero h₀.1, Nat.Prime.ne_zero h₀.2]
  
  have h₉ : n = 2 := by
    have h₉₁ : m = k + t := h₅
    have h₉₂ : k = n := h₈
    have h₉₃ : t = 1 := h₇
    have h₉₄ : m = n + 1 := by
      subst_vars
      <;> ring_nf at *
      <;> omega
    have h₉₅ : Nat.Prime m := h₀.1
    have h₉₆ : Nat.Prime n := h₀.2
    have h₉₇ : n = 2 := by
      by_contra h
      have h₉₈ := h₉₆.eq_two_or_odd
      have h₉₉ := h₉₅.eq_two_or_odd
      cases' h₉₈ with h₉₈ h₉₈
      · exfalso
        omega
      · cases' h₉₉ with h₉₉ h₉₉
        · exfalso
          have h₁₀₀ := h₉₅.two_le
          have h₁₀₁ := h₉₆.two_le
          omega
        · have h₁₀₂ : m % 2 = 0 := by
            omega
          have h₁₀₃ : m = 2 := by
            have h₁₀₄ := h₉₅.eq_two_or_odd
            cases' h₁₀₄ with h₁₀₄ h₁₀₄
            · omega
            · omega
          have h₁₀₅ : n = 1 := by
            omega
          have h₁₀₆ : Nat.Prime n := h₀.2
          have h₁₀₇ := h₁₀₆.eq_two_or_odd
          cases' h₁₀₇ with h₁₀₇ h₁₀₇
          · omega
          · omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
          <;> omega
        <;> omega
        <;> omega
        <;> omega
    exact h₉₇
  
  have h₁₀ : m = 3 := by
    have h₁₀₁ : m = k + t := h₅
    have h₁₀₂ : k = n := h₈
    have h₁₀₃ : t = 1 := h₇
    have h₁₀₄ : n = 2 := h₉
    have h₁₀₅ : m = 3 := by
      subst_vars
      <;> norm_num at *
      <;> omega
    exact h₁₀₅
  
  have h₁₁ : k = 2 := by
    have h₁₁₁ : k = n := h₈
    have h₁₁₂ : n = 2 := h₉
    linarith
  
  have h₁₂ : t = 1 := by
    exact h₇
  
  have h₁₃ : m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
    subst_vars
    <;> norm_num at *
    <;> decide
  
  apply h₁₃