import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1981_p6
  (f : ℕ → ℕ → ℕ)
  (g : ℕ → ℕ)
  (h₀ : ∀ y, f 0 y = y + 1)
  (h₁ : ∀ x, f (x + 1) 0 = f x 1)
  (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y))
  (h₃ : g 0 = 2)
  (h₄ : ∀ n, g (n + 1) = 2^(g n)) :
  f 4 1981 = g 1983 - 3 := by
  have h_f₁ : ∀ y, f 1 y = y + 2 := by
    intro y
    induction y with
    | zero =>
      have h₁₀ : f 1 0 = f 0 1 := by
        have h₁₀₁ := h₁ 0
        simp at h₁₀₁ ⊢
        <;> linarith
      have h₁₁ : f 0 1 = 2 := by
        have h₁₁₁ := h₀ 1
        simp at h₁₁₁ ⊢
        <;> linarith
      have h₁₂ : f 1 0 = 2 := by linarith
      simp [h₁₂]
      <;> norm_num
    | succ y ih =>
      have h₂₀ : f 1 (y + 1) = f 0 (f 1 y) := by
        have h₂₀₁ := h₂ 0 y
        simp at h₂₀₁ ⊢
        <;> linarith
      have h₂₁ : f 0 (f 1 y) = f 1 y + 1 := by
        have h₂₁₁ := h₀ (f 1 y)
        simp at h₂₁₁ ⊢
        <;> linarith
      have h₂₂ : f 1 (y + 1) = f 1 y + 1 := by linarith
      have h₂₃ : f 1 (y + 1) = (y + 1) + 2 := by
        rw [h₂₂, ih]
        <;> ring
        <;> omega
      exact h₂₃
  
  have h_f₂ : ∀ y, f 2 y = 2 * y + 3 := by
    intro y
    induction y with
    | zero =>
      have h₂₀ : f 2 0 = f 1 1 := by
        have h₂₀₁ := h₁ 1
        simp at h₂₀₁ ⊢
        <;> linarith
      have h₂₁ : f 1 1 = 3 := by
        have h₂₁₁ := h_f₁ 1
        simp at h₂₁₁ ⊢
        <;> linarith
      have h₂₂ : f 2 0 = 3 := by linarith
      simp [h₂₂]
      <;> norm_num
    | succ y ih =>
      have h₃₀ : f 2 (y + 1) = f 1 (f 2 y) := by
        have h₃₀₁ := h₂ 1 y
        simp at h₃₀₁ ⊢
        <;> linarith
      have h₃₁ : f 1 (f 2 y) = f 2 y + 2 := by
        have h₃₁₁ := h_f₁ (f 2 y)
        simp at h₃₁₁ ⊢
        <;> linarith
      have h₃₂ : f 2 (y + 1) = f 2 y + 2 := by linarith
      have h₃₃ : f 2 (y + 1) = 2 * (y + 1) + 3 := by
        rw [h₃₂, ih]
        <;> ring
        <;> omega
      exact h₃₃
  
  have h_f₃ : ∀ y, f 3 y = 2 ^ (y + 3) - 3 := by
    intro y
    have h₃ : ∀ y, f 3 y = 2 ^ (y + 3) - 3 := by
      intro y
      induction y with
      | zero =>
        have h₃₀ : f 3 0 = f 2 1 := by
          have h₃₀₁ := h₁ 2
          simp at h₃₀₁ ⊢
          <;> linarith
        have h₃₁ : f 2 1 = 5 := by
          have h₃₁₁ := h_f₂ 1
          simp at h₃₁₁ ⊢
          <;> linarith
        have h₃₂ : f 3 0 = 5 := by linarith
        have h₃₃ : (2 : ℕ) ^ (0 + 3) - 3 = 5 := by norm_num
        simp [h₃₂, h₃₃]
        <;> norm_num
      | succ y ih =>
        have h₄₀ : f 3 (y + 1) = f 2 (f 3 y) := by
          have h₄₀₁ := h₂ 2 y
          simp at h₄₀₁ ⊢
          <;> linarith
        have h₄₁ : f 2 (f 3 y) = 2 * f 3 y + 3 := by
          have h₄₁₁ := h_f₂ (f 3 y)
          simp at h₄₁₁ ⊢
          <;> linarith
        have h₄₂ : f 3 (y + 1) = 2 * f 3 y + 3 := by linarith
        have h₄₃ : f 3 (y + 1) = 2 ^ ((y + 1) + 3) - 3 := by
          rw [h₄₂, ih]
          have h₅ : 2 * (2 ^ (y + 3) - 3) + 3 = 2 ^ ((y + 1) + 3) - 3 := by
            have h₅₁ : y + 3 ≥ 3 := by omega
            have h₅₂ : 2 ^ (y + 3) ≥ 2 ^ 3 := by
              apply Nat.pow_le_pow_of_le_right
              <;> norm_num
              <;> omega
            have h₅₃ : 2 ^ (y + 3) ≥ 8 := by
              have h₅₄ : 2 ^ 3 = 8 := by norm_num
              linarith
            have h₅₄ : 2 ^ (y + 3) - 3 ≥ 5 := by
              have h₅₅ : 2 ^ (y + 3) ≥ 8 := by omega
              omega
            have h₅₅ : 2 * (2 ^ (y + 3) - 3) + 3 = 2 ^ ((y + 1) + 3) - 3 := by
              have h₅₅₁ : 2 ^ ((y + 1) + 3) = 2 ^ (y + 4) := by
                ring_nf
              rw [h₅₅₁]
              have h₅₅₂ : 2 ^ (y + 4) = 2 ^ (y + 3 + 1) := by ring_nf
              rw [h₅₅₂]
              have h₅₅₃ : 2 ^ (y + 3 + 1) = 2 * 2 ^ (y + 3) := by
                simp [Nat.pow_succ, Nat.mul_add]
                <;> ring_nf
              rw [h₅₅₃]
              have h₅₅₄ : 2 ^ (y + 3) - 3 ≥ 0 := by omega
              have h₅₅₅ : 2 * (2 ^ (y + 3) - 3) + 3 = 2 * 2 ^ (y + 3) - 3 := by
                omega
              omega
            exact h₅₅
          omega
        exact h₄₃
    exact h₃ y
  
  have h_f₄ : ∀ y, f 4 (y + 1) = f 3 (f 4 y) := by
    intro y
    have h₄ := h₂ 3 y
    simp at h₄ ⊢
    <;> simp_all [Nat.add_assoc]
    <;> ring_nf at *
    <;> omega
  
  have h_main : ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
    intro y
    have h₅ : f 4 (y + 1) = f 3 (f 4 y) := by
      apply h_f₄
    rw [h₅]
    have h₆ : f 3 (f 4 y) = 2 ^ (f 4 y + 3) - 3 := by
      have h₆₁ : f 3 (f 4 y) = 2 ^ (f 4 y + 3) - 3 := by
        rw [h_f₃]
        <;> simp [Nat.add_assoc]
      rw [h₆₁]
    rw [h₆]
    <;> simp [Nat.add_assoc]
  
  exact h_main