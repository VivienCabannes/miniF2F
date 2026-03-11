import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_521
  (m n : ℕ)
  (h₀ : Even m)
  (h₁ : Even n)
  (h₂ : m - n = 2)
  (h₃ : m * n = 288) :
  m = 18 := by
  have h₄ : n ≥ 2 := by
    by_contra h
    -- Assume n < 2
    have h₅ : n = 0 := by
      have h₅₁ : n ≤ 1 := by
        omega
      have h₅₂ : Even n := h₁
      have h₅₃ : n % 2 = 0 := by
        rw [even_iff_two_dvd] at h₅₂
        omega
      have h₅₄ : n = 0 := by
        omega
      exact h₅₄
    -- If n = 0, then m - n = m = 2
    have h₆ : m = 2 := by
      have h₆₁ : m - n = 2 := h₂
      have h₆₂ : n = 0 := h₅
      rw [h₆₂] at h₆₁
      omega
    -- If m = 2 and n = 0, then m * n = 0 ≠ 288
    have h₇ : m * n = 288 := h₃
    rw [h₅, h₆] at h₇
    norm_num at h₇
    <;> simp_all (config := {decide := true})
    <;> omega
  
  have h₅ : m = n + 2 := by
    have h₅₁ : m ≥ n + 2 := by
      by_contra h₅₁
      have h₅₂ : m < n + 2 := by omega
      have h₅₃ : m ≤ n + 1 := by omega
      have h₅₄ : m - n ≤ 1 := by
        have h₅₄₁ : m ≤ n + 1 := h₅₃
        have h₅₄₂ : m - n ≤ 1 := by
          omega
        exact h₅₄₂
      have h₅₅ : m - n = 2 := h₂
      omega
    have h₅₂ : m < n + 3 := by
      by_contra h₅₂
      have h₅₃ : m ≥ n + 3 := by omega
      have h₅₄ : m - n ≥ 3 := by
        have h₅₄₁ : m ≥ n + 3 := h₅₃
        have h₅₄₂ : m - n ≥ 3 := by
          omega
        exact h₅₄₂
      have h₅₅ : m - n = 2 := h₂
      omega
    have h₅₃ : m = n + 2 := by
      omega
    exact h₅₃
  
  have h₆ : n = 16 := by
    rw [h₅] at h₃
    have h₆₁ : (n + 2) * n = 288 := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h₃
    have h₆₂ : n ≤ 16 := by
      by_contra h₆₂
      have h₆₃ : n ≥ 17 := by omega
      have h₆₄ : (n + 2) * n > 288 := by
        have h₆₅ : n ≥ 17 := h₆₃
        have h₆₆ : (n + 2) * n ≥ 19 * n := by
          nlinarith
        have h₆₇ : 19 * n > 288 := by
          nlinarith
        nlinarith
      nlinarith
    interval_cases n <;> norm_num at h₆₁ ⊢ <;>
      (try omega) <;> (try norm_num at h₅ ⊢ <;> omega)
    <;>
      (try simp_all [Nat.even_iff, Nat.odd_iff, Nat.mod_eq_of_lt])
    <;>
      (try omega)
  
  have h₇ : m = 18 := by
    rw [h₅, h₆]
    <;> norm_num
    <;> omega
  
  apply h₇