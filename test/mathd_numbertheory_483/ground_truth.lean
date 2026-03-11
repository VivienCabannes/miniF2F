import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_483
  (a : ℕ → ℕ)
  (h₀ : a 1 = 1)
  (h₁ : a 2 = 1)
  (h₂ : ∀ n, a (n + 2) = a (n + 1) + a n) :
  (a 100) % 4 = 3 := by
  have h₃ : a 0 = 0 := by
    have h₄ := h₂ 0
    simp [h₀, h₁] at h₄
    <;> omega
  
  have h₄ : a 3 = 2 := by
    have h₅ := h₂ 1
    have h₆ := h₂ 2
    have h₇ := h₂ 3
    simp [h₀, h₁, h₃] at h₅ h₆ h₇
    <;> omega
  
  have h₅ : a 4 = 3 := by
    have h₅ := h₂ 2
    have h₆ := h₂ 3
    have h₇ := h₂ 4
    simp [h₀, h₁, h₃, h₄] at h₅ h₆ h₇
    <;> omega
  
  have h₆ : a 5 = 5 := by
    have h₆ := h₂ 3
    have h₇ := h₂ 4
    have h₈ := h₂ 5
    simp [h₀, h₁, h₃, h₄, h₅] at h₆ h₇ h₈
    <;> omega
  
  have h₇ : a 6 = 8 := by
    have h₇ := h₂ 4
    have h₈ := h₂ 5
    have h₉ := h₂ 6
    simp [h₀, h₁, h₃, h₄, h₅, h₆] at h₇ h₈ h₉
    <;> omega
  
  have h₈ : a 7 = 13 := by
    have h₈ := h₂ 5
    have h₉ := h₂ 6
    have h₁₀ := h₂ 7
    simp [h₀, h₁, h₃, h₄, h₅, h₆, h₇] at h₈ h₉ h₁₀
    <;> omega
  
  have h₉ : a 8 = 21 := by
    have h₉ := h₂ 6
    have h₁₀ := h₂ 7
    have h₁₁ := h₂ 8
    simp [h₀, h₁, h₃, h₄, h₅, h₆, h₇, h₈] at h₉ h₁₀ h₁₁
    <;> omega
  
  have h₁₀ : a 9 = 34 := by
    have h₁₀ := h₂ 7
    have h₁₁ := h₂ 8
    have h₁₂ := h₂ 9
    simp [h₀, h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉] at h₁₀ h₁₁ h₁₂
    <;> omega
  
  have h₁₁ : a 10 = 55 := by
    have h₁₁ := h₂ 8
    have h₁₂ := h₂ 9
    have h₁₃ := h₂ 10
    simp [h₀, h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀] at h₁₁ h₁₂ h₁₃
    <;> omega
  
  have h₁₂ : ∀ n, a (n + 6) % 4 = a n % 4 := by
    intro n
    have h₁₃ : a (n + 6) = 8 * a (n + 1) + 5 * a n := by
      have h₁₄ := h₂ n
      have h₁₅ := h₂ (n + 1)
      have h₁₆ := h₂ (n + 2)
      have h₁₇ := h₂ (n + 3)
      have h₁₈ := h₂ (n + 4)
      have h₁₉ := h₂ (n + 5)
      have h₂₀ := h₂ (n + 6)
      have h₂₁ := h₂ (n + 7)
      have h₂₂ := h₂ (n + 8)
      have h₂₃ := h₂ (n + 9)
      simp [add_assoc, add_comm, add_left_comm] at h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ h₂₁ h₂₂ h₂₃ ⊢
      ring_nf at h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ h₂₁ h₂₂ h₂₃ ⊢
      <;>
      (try omega) <;>
      (try nlinarith) <;>
      (try ring_nf at h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ h₂₁ h₂₂ h₂₃ ⊢ <;> omega) <;>
      (try nlinarith) <;>
      (try omega) <;>
      (try nlinarith) <;>
      (try omega)
    rw [h₁₃]
    have h₂₄ : (8 * a (n + 1) + 5 * a n) % 4 = a n % 4 := by
      have h₂₅ : (8 * a (n + 1) + 5 * a n) % 4 = (a n % 4) := by
        have h₂₆ : a (n + 1) % 4 = a (n + 1) % 4 := rfl
        have h₂₇ : a n % 4 = a n % 4 := rfl
        have h₂₈ : (8 * a (n + 1) + 5 * a n) % 4 = (a n % 4) := by
          have h₂₉ : (8 * a (n + 1) + 5 * a n) % 4 = ((8 * a (n + 1)) % 4 + (5 * a n) % 4) % 4 := by
            omega
          rw [h₂₉]
          have h₃₀ : (8 * a (n + 1)) % 4 = 0 := by
            have h₃₁ : (8 * a (n + 1)) % 4 = 0 := by
              omega
            exact h₃₁
          have h₃₂ : (5 * a n) % 4 = (a n) % 4 := by
            have h₃₃ : (5 * a n) % 4 = (a n) % 4 := by
              omega
            exact h₃₃
          omega
        exact h₂₈
      omega
    omega
  
  have h₁₃ : a 100 % 4 = 3 := by
    have h₁₄ : a 100 % 4 = 3 := by
      have h₁₅ : a 100 % 4 = a 4 % 4 := by
        have h₁₆ : a 100 % 4 = a 4 % 4 := by
          have h₁₇ : a 100 % 4 = a 4 % 4 := by
            have h₁₈ : a 100 % 4 = a 4 % 4 := by
              -- Use the periodicity to reduce the index
              have h₁₉ := h₁₂ 94
              have h₂₀ := h₁₂ 88
              have h₂₁ := h₁₂ 82
              have h₂₂ := h₁₂ 76
              have h₂₃ := h₁₂ 70
              have h₂₄ := h₁₂ 64
              have h₂₅ := h₁₂ 58
              have h₂₆ := h₁₂ 52
              have h₂₇ := h₁₂ 46
              have h₂₈ := h₁₂ 40
              have h₂₉ := h₁₂ 34
              have h₃₀ := h₁₂ 28
              have h₃₁ := h₁₂ 22
              have h₃₂ := h₁₂ 16
              have h₃₃ := h₁₂ 10
              have h₃₄ := h₁₂ 4
              norm_num at h₁₉ h₂₀ h₂₁ h₂₂ h₂₃ h₂₄ h₂₅ h₂₆ h₂₇ h₂₈ h₂₉ h₃₀ h₃₁ h₃₂ h₃₃ h₃₄ ⊢
              <;>
                (try omega) <;>
                (try ring_nf at h₁₉ h₂₀ h₂₁ h₂₂ h₂₃ h₂₄ h₂₅ h₂₆ h₂₇ h₂₈ h₂₉ h₃₀ h₃₁ h₃₂ h₃₃ h₃₄ ⊢) <;>
                (try omega) <;>
                (try ring_nf) <;>
                (try omega)
            exact h₁₈
          exact h₁₇
        exact h₁₆
      have h₁₅₁ : a 4 % 4 = 3 := by
        norm_num [h₅]
      rw [h₁₅]
      exact h₁₅₁
    exact h₁₄
  
  exact h₁₃