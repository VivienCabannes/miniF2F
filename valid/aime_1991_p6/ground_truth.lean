import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1991_p6 (r : ℝ) (h₀ : (∑ k ∈ Finset.Icc (19 : ℕ) 91, Int.floor (r + k / 100)) = 546) :
  Int.floor (100 * r) = 743 := by
  have h₁ : r + 57 / 100 ≥ 8 := by
    by_contra h
    have h₂ : r + 57 / 100 < 8 := by linarith
    have h₃ : ∀ (k : ℕ), k ∈ Finset.Icc 19 91 → k ≤ 57 → Int.floor (r + k / 100) ≤ 7 := by
      intro k hk hk'
      have h₄ : (k : ℝ) ≤ 57 := by exact_mod_cast hk'
      have h₅ : r + k / 100 < 8 := by
        have h₅₁ : (k : ℝ) ≤ 57 := by exact_mod_cast hk'
        have h₅₂ : r + (k : ℝ) / 100 < 8 := by
          have h₅₃ : r + (57 : ℝ) / 100 < 8 := by exact_mod_cast h₂
          have h₅₄ : (k : ℝ) ≤ 57 := by exact_mod_cast hk'
          have h₅₅ : (k : ℝ) / 100 ≤ (57 : ℝ) / 100 := by
            exact div_le_div_of_le_of_nonneg h₅₄ (by norm_num)
          linarith
        simpa using h₅₂
      have h₆ : Int.floor (r + k / 100) ≤ 7 := by
        have h₆₁ : Int.floor (r + k / 100) < 8 := by
          apply Int.floor_lt.mpr
          norm_num at h₅ ⊢
          <;> linarith
        have h₆₂ : Int.floor (r + k / 100) ≤ 7 := by
          omega
        exact h₆₂
      exact h₆
    have h₄ : ∀ (k : ℕ), k ∈ Finset.Icc 19 91 → k ≥ 58 → Int.floor (r + k / 100) ≤ 8 := by
      intro k hk hk'
      have h₅ : (k : ℝ) ≥ 58 := by exact_mod_cast hk'
      have h₆ : r + k / 100 < 9 := by
        have h₆₁ : (k : ℝ) ≤ 91 := by
          norm_num [Finset.mem_Icc] at hk
          <;> exact_mod_cast hk.2
        have h₆₂ : r + (k : ℝ) / 100 < 9 := by
          have h₆₃ : r + (57 : ℝ) / 100 < 8 := by exact_mod_cast h₂
          have h₆₄ : (k : ℝ) ≥ 58 := by exact_mod_cast hk'
          have h₆₅ : (k : ℝ) / 100 ≤ (91 : ℝ) / 100 := by
            have h₆₅₁ : (k : ℝ) ≤ 91 := by exact_mod_cast (by norm_num [Finset.mem_Icc] at hk; exact hk.2)
            have h₆₅₂ : (k : ℝ) / 100 ≤ (91 : ℝ) / 100 := by
              exact div_le_div_of_le_of_nonneg h₆₅₁ (by norm_num)
            exact h₆₅₂
          have h₆₆ : r + (k : ℝ) / 100 < 9 := by
            linarith
          simpa using h₆₆
        simpa using h₆₂
      have h₇ : Int.floor (r + k / 100) ≤ 8 := by
        have h₇₁ : Int.floor (r + k / 100) < 9 := by
          apply Int.floor_lt.mpr
          norm_num at h₆ ⊢
          <;> linarith
        have h₇₂ : Int.floor (r + k / 100) ≤ 8 := by
          omega
        exact h₇₂
      exact h₇
    have h₅ : (∑ k in Finset.Icc (19 : ℕ) 91, Int.floor (r + k / 100)) ≤ 545 := by
      have h₅₁ : (∑ k in Finset.Icc (19 : ℕ) 91, Int.floor (r + k / 100)) ≤ ∑ k in Finset.Icc (19 : ℕ) 91, (if k ≤ 57 then 7 else 8 : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        have h₅₂ : k ∈ Finset.Icc 19 91 := by simpa using hk
        have h₅₃ : 19 ≤ k ∧ k ≤ 91 := by simpa using h₅₂
        by_cases h₅₄ : k ≤ 57
        · have h₅₅ : Int.floor (r + k / 100) ≤ 7 := by
            exact h₃ k h₅₂ (by linarith)
          have h₅₆ : (if k ≤ 57 then 7 else 8 : ℤ) = 7 := by
            simp [h₅₄]
          rw [h₅₆]
          exact h₅₅
        · have h₅₅ : k ≥ 58 := by
            omega
          have h₅₆ : Int.floor (r + k / 100) ≤ 8 := by
            exact h₄ k h₅₂ (by omega)
          have h₅₇ : (if k ≤ 57 then 7 else 8 : ℤ) = 8 := by
            simp [h₅₄]
          rw [h₅₇]
          have h₅₈ : Int.floor (r + k / 100) ≤ 8 := by
            exact h₄ k h₅₂ (by omega)
          linarith
      have h₅₂ : ∑ k in Finset.Icc (19 : ℕ) 91, (if k ≤ 57 then 7 else 8 : ℤ) = 545 := by
        norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_singleton]
        <;> rfl
      linarith
    linarith
  
  have h₂ : r + 56 / 100 < 8 := by
    by_contra h
    have h₂ : r + 56 / 100 ≥ 8 := by linarith
    have h₃ : ∀ (k : ℕ), k ∈ Finset.Icc 19 91 → k ≥ 56 → Int.floor (r + k / 100) ≥ 8 := by
      intro k hk hk'
      have h₄ : (k : ℝ) ≥ 56 := by exact_mod_cast hk'
      have h₅ : r + k / 100 ≥ 8 := by
        have h₅₁ : (k : ℝ) ≥ 56 := by exact_mod_cast hk'
        have h₅₂ : r + (k : ℝ) / 100 ≥ 8 := by
          have h₅₃ : r + (56 : ℝ) / 100 ≥ 8 := by exact_mod_cast h₂
          have h₅₄ : (k : ℝ) ≥ 56 := by exact_mod_cast hk'
          have h₅₅ : (k : ℝ) / 100 ≥ (56 : ℝ) / 100 := by
            exact div_le_div_of_le_of_nonneg h₅₄ (by norm_num)
          linarith
        simpa using h₅₂
      have h₆ : Int.floor (r + k / 100) ≥ 8 := by
        have h₆₁ : (8 : ℝ) ≤ r + k / 100 := by exact_mod_cast h₅
        have h₆₂ : (8 : ℤ) ≤ Int.floor (r + k / 100) := by
          exact Int.le_floor.mpr h₆₁
        exact_mod_cast h₆₂
      exact h₆
    have h₄ : ∀ (k : ℕ), k ∈ Finset.Icc 19 91 → k < 56 → Int.floor (r + k / 100) ≥ 7 := by
      intro k hk hk'
      have h₅ : (k : ℝ) < 56 := by exact_mod_cast hk'
      have h₆ : r + k / 100 ≥ 7 := by
        have h₆₁ : (k : ℝ) ≥ 19 := by
          norm_num [Finset.mem_Icc] at hk
          <;> exact_mod_cast hk.1
        have h₆₂ : r + (k : ℝ) / 100 ≥ 7 := by
          have h₆₃ : r + (56 : ℝ) / 100 ≥ 8 := by exact_mod_cast h₂
          have h₆₄ : (k : ℝ) < 56 := by exact_mod_cast hk'
          have h₆₅ : (k : ℝ) / 100 ≤ (56 : ℝ) / 100 := by
            exact div_le_div_of_le_of_nonneg (by linarith) (by norm_num)
          have h₆₆ : r + (k : ℝ) / 100 ≥ 7 := by
            have h₆₇ : r + (19 : ℝ) / 100 ≥ 7 := by
              have h₆₇₁ : r + (57 : ℝ) / 100 ≥ 8 := by exact_mod_cast h₁
              have h₆₇₂ : r + (19 : ℝ) / 100 ≥ 7 := by
                linarith
              exact h₆₇₂
            linarith
          simpa using h₆₆
        simpa using h₆₂
      have h₇ : Int.floor (r + k / 100) ≥ 7 := by
        have h₇₁ : (7 : ℝ) ≤ r + k / 100 := by exact_mod_cast h₆
        have h₇₂ : (7 : ℤ) ≤ Int.floor (r + k / 100) := by
          exact Int.le_floor.mpr h₇₁
        exact_mod_cast h₇₂
      exact h₇
    have h₅ : (∑ k in Finset.Icc (19 : ℕ) 91, Int.floor (r + k / 100)) ≥ 547 := by
      have h₅₁ : (∑ k in Finset.Icc (19 : ℕ) 91, Int.floor (r + k / 100)) ≥ ∑ k in Finset.Icc (19 : ℕ) 91, (if k ≥ 56 then 8 else 7 : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        have h₅₂ : k ∈ Finset.Icc 19 91 := by simpa using hk
        have h₅₃ : 19 ≤ k ∧ k ≤ 91 := by simpa using h₅₂
        by_cases h₅₄ : k ≥ 56
        · have h₅₅ : Int.floor (r + k / 100) ≥ 8 := by
            exact h₃ k h₅₂ (by linarith)
          have h₅₆ : (if k ≥ 56 then 8 else 7 : ℤ) = 8 := by
            simp [h₅₄]
          rw [h₅₆]
          exact h₅₅
        · have h₅₅ : k < 56 := by
            omega
          have h₅₆ : Int.floor (r + k / 100) ≥ 7 := by
            exact h₄ k h₅₂ (by omega)
          have h₅₇ : (if k ≥ 56 then 8 else 7 : ℤ) = 7 := by
            simp [h₅₄]
          rw [h₅₇]
          exact h₅₆
      have h₅₂ : ∑ k in Finset.Icc (19 : ℕ) 91, (if k ≥ 56 then 8 else 7 : ℤ) = 547 := by
        norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_singleton]
        <;> rfl
      linarith
    linarith
  
  have h₃ : Int.floor (100 * r) = 743 := by
    have h₄ : (743 : ℝ) ≤ 100 * r := by
      have h₄₁ : (r + (57 : ℝ) / 100 ≥ 8) := by exact_mod_cast h₁
      have h₄₂ : (100 * r ≥ 743) := by
        norm_num at h₄₁ ⊢
        <;> linarith
      exact_mod_cast h₄₂
    have h₅ : (100 * r : ℝ) < 744 := by
      have h₅₁ : (r + (56 : ℝ) / 100 < 8) := by exact_mod_cast h₂
      have h₅₂ : (100 * r : ℝ) < 744 := by
        norm_num at h₅₁ ⊢
        <;> linarith
      exact h₅₂
    have h₆ : Int.floor (100 * r : ℝ) = 743 := by
      rw [Int.floor_eq_iff]
      norm_num at h₄ h₅ ⊢
      constructor <;>
      (try norm_num at h₁ h₂ ⊢) <;>
      (try linarith) <;>
      (try assumption) <;>
      (try norm_num) <;>
      (try linarith)
    exact_mod_cast h₆
  exact h₃