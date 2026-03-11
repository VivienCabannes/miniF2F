import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2021_p8
  (d : ℕ → ℕ)
  (h₀ : d 0 = 0)
  (h₁ : d 1 = 0)
  (h₂ : d 2 = 1)
  (h₃ : ∀ n≥3, d n = d (n - 1) + d (n - 3)) :
  Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  have h₄ : ∀ n : ℕ, (n % 7 = 0 → d n % 2 = 0) ∧ (n % 7 = 1 → d n % 2 = 0) ∧ (n % 7 = 2 → d n % 2 = 1) ∧ (n % 7 = 3 → d n % 2 = 1) ∧ (n % 7 = 4 → d n % 2 = 1) ∧ (n % 7 = 5 → d n % 2 = 0) ∧ (n % 7 = 6 → d n % 2 = 1) := by
    intro n
    have h₄₁ : (n % 7 = 0 → d n % 2 = 0) ∧ (n % 7 = 1 → d n % 2 = 0) ∧ (n % 7 = 2 → d n % 2 = 1) ∧ (n % 7 = 3 → d n % 2 = 1) ∧ (n % 7 = 4 → d n % 2 = 1) ∧ (n % 7 = 5 → d n % 2 = 0) ∧ (n % 7 = 6 → d n % 2 = 1) := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        have h₅ : n % 7 = 0 → d n % 2 = 0 := by
          intro h₅
          have h₆ : n % 7 = 0 := h₅
          have h₇ : d n % 2 = 0 := by
            by_cases h₈ : n ≥ 3
            · have h₉ : d n = d (n - 1) + d (n - 3) := h₃ n h₈
              rw [h₉]
              have h₁₀ : (n - 1) % 7 = 6 := by
                have h₁₁ : n % 7 = 0 := h₆
                omega
              have h₁₁ : (n - 3) % 7 = 4 := by
                have h₁₂ : n % 7 = 0 := h₆
                omega
              have h₁₂ : d (n - 1) % 2 = 1 := by
                have h₁₃ := ih ((n - 1)) (by
                  have h₁₄ : n - 1 < n := by
                    omega
                  omega)
                have h₁₄ := h₁₃.2.2.2.2.2.2 (by omega)
                omega
              have h₁₃ : d (n - 3) % 2 = 1 := by
                have h₁₄ := ih ((n - 3)) (by
                  have h₁₅ : n - 3 < n := by
                    omega
                  omega)
                have h₁₅ := h₁₄.2.2.2.2.1 (by omega)
                omega
              omega
            · have h₉ : n = 0 ∨ n = 1 ∨ n = 2 := by
                omega
              rcases h₉ with (rfl | rfl | rfl) <;> simp [h₀, h₁, h₂, Nat.mod_eq_of_lt] <;> norm_num
              <;> try omega
          exact h₇
        have h₆ : n % 7 = 1 → d n % 2 = 0 := by
          intro h₆
          have h₇ : n % 7 = 1 := h₆
          have h₈ : d n % 2 = 0 := by
            by_cases h₉ : n ≥ 3
            · have h₁₀ : d n = d (n - 1) + d (n - 3) := h₃ n h₉
              rw [h₁₀]
              have h₁₁ : (n - 1) % 7 = 0 := by
                have h₁₂ : n % 7 = 1 := h₇
                omega
              have h₁₂ : (n - 3) % 7 = 5 := by
                have h₁₃ : n % 7 = 1 := h₇
                omega
              have h₁₃ : d (n - 1) % 2 = 0 := by
                have h₁₄ := ih ((n - 1)) (by
                  have h₁₅ : n - 1 < n := by
                    omega
                  omega)
                have h₁₅ := h₁₄.1 (by omega)
                omega
              have h₁₄ : d (n - 3) % 2 = 0 := by
                have h₁₅ := ih ((n - 3)) (by
                  have h₁₆ : n - 3 < n := by
                    omega
                  omega)
                have h₁₆ := h₁₅.2.2.2.2.2.1 (by omega)
                omega
              omega
            · have h₉ : n = 0 ∨ n = 1 ∨ n = 2 := by
                omega
              rcases h₉ with (rfl | rfl | rfl) <;> simp [h₀, h₁, h₂, Nat.mod_eq_of_lt] <;> norm_num
              <;> try omega
          exact h₈
        have h₇ : n % 7 = 2 → d n % 2 = 1 := by
          intro h₇
          have h₈ : n % 7 = 2 := h₇
          have h₉ : d n % 2 = 1 := by
            by_cases h₁₀ : n ≥ 3
            · have h₁₁ : d n = d (n - 1) + d (n - 3) := h₃ n h₁₀
              rw [h₁₁]
              have h₁₂ : (n - 1) % 7 = 1 := by
                have h₁₃ : n % 7 = 2 := h₈
                omega
              have h₁₃ : (n - 3) % 7 = 6 := by
                have h₁₄ : n % 7 = 2 := h₈
                omega
              have h₁₄ : d (n - 1) % 2 = 0 := by
                have h₁₅ := ih ((n - 1)) (by
                  have h₁₆ : n - 1 < n := by
                    omega
                  omega)
                have h₁₆ := h₁₅.2.1 (by omega)
                omega
              have h₁₅ : d (n - 3) % 2 = 1 := by
                have h₁₆ := ih ((n - 3)) (by
                  have h₁₇ : n - 3 < n := by
                    omega
                  omega)
                have h₁₇ := h₁₆.2.2.2.2.2.2 (by omega)
                omega
              omega
            · have h₁₀ : n = 0 ∨ n = 1 ∨ n = 2 := by
                omega
              rcases h₁₀ with (rfl | rfl | rfl) <;> simp [h₀, h₁, h₂, Nat.mod_eq_of_lt] <;> norm_num
              <;> try omega
          exact h₉
        have h₈ : n % 7 = 3 → d n % 2 = 1 := by
          intro h₈
          have h₉ : n % 7 = 3 := h₈
          have h₁₀ : d n % 2 = 1 := by
            by_cases h₁₁ : n ≥ 3
            · have h₁₂ : d n = d (n - 1) + d (n - 3) := h₃ n h₁₁
              rw [h₁₂]
              have h₁₃ : (n - 1) % 7 = 2 := by
                have h₁₄ : n % 7 = 3 := h₉
                omega
              have h₁₄ : (n - 3) % 7 = 0 := by
                have h₁₅ : n % 7 = 3 := h₉
                omega
              have h₁₅ : d (n - 1) % 2 = 1 := by
                have h₁₆ := ih ((n - 1)) (by
                  have h₁₇ : n - 1 < n := by
                    omega
                  omega)
                have h₁₇ := h₁₆.2.2.1 (by omega)
                omega
              have h₁₆ : d (n - 3) % 2 = 0 := by
                have h₁₇ := ih ((n - 3)) (by
                  have h₁₈ : n - 3 < n := by
                    omega
                  omega)
                have h₁₈ := h₁₇.1 (by omega)
                omega
              omega
            · have h₁₁ : n = 0 ∨ n = 1 ∨ n = 2 := by
                omega
              rcases h₁₁ with (rfl | rfl | rfl) <;> simp [h₀, h₁, h₂, Nat.mod_eq_of_lt] <;> norm_num
              <;> try omega
          exact h₁₀
        have h₉ : n % 7 = 4 → d n % 2 = 1 := by
          intro h₉
          have h₁₀ : n % 7 = 4 := h₉
          have h₁₁ : d n % 2 = 1 := by
            by_cases h₁₂ : n ≥ 3
            · have h₁₃ : d n = d (n - 1) + d (n - 3) := h₃ n h₁₂
              rw [h₁₃]
              have h₁₄ : (n - 1) % 7 = 3 := by
                have h₁₅ : n % 7 = 4 := h₁₀
                omega
              have h₁₅ : (n - 3) % 7 = 1 := by
                have h₁₆ : n % 7 = 4 := h₁₀
                omega
              have h₁₆ : d (n - 1) % 2 = 1 := by
                have h₁₇ := ih ((n - 1)) (by
                  have h₁₈ : n - 1 < n := by
                    omega
                  omega)
                have h₁₈ := h₁₇.2.2.2.1 (by omega)
                omega
              have h₁₇ : d (n - 3) % 2 = 0 := by
                have h₁₈ := ih ((n - 3)) (by
                  have h₁₉ : n - 3 < n := by
                    omega
                  omega)
                have h₁₉ := h₁₈.2.1 (by omega)
                omega
              omega
            · have h₁₂ : n = 0 ∨ n = 1 ∨ n = 2 := by
                omega
              rcases h₁₂ with (rfl | rfl | rfl) <;> simp [h₀, h₁, h₂, Nat.mod_eq_of_lt] <;> norm_num
              <;> try omega
          exact h₁₁
        have h₁₀ : n % 7 = 5 → d n % 2 = 0 := by
          intro h₁₀
          have h₁₁ : n % 7 = 5 := h₁₀
          have h₁₂ : d n % 2 = 0 := by
            by_cases h₁₃ : n ≥ 3
            · have h₁₄ : d n = d (n - 1) + d (n - 3) := h₃ n h₁₃
              rw [h₁₄]
              have h₁₅ : (n - 1) % 7 = 4 := by
                have h₁₆ : n % 7 = 5 := h₁₁
                omega
              have h₁₆ : (n - 3) % 7 = 2 := by
                have h₁₇ : n % 7 = 5 := h₁₁
                omega
              have h₁₇ : d (n - 1) % 2 = 1 := by
                have h₁₈ := ih ((n - 1)) (by
                  have h₁₉ : n - 1 < n := by
                    omega
                  omega)
                have h₁₉ := h₁₈.2.2.2.2.1 (by omega)
                omega
              have h₁₈ : d (n - 3) % 2 = 1 := by
                have h₁₉ := ih ((n - 3)) (by
                  have h₂₀ : n - 3 < n := by
                    omega
                  omega)
                have h₂₀ := h₁₉.2.2.1 (by omega)
                omega
              omega
            · have h₁₃ : n = 0 ∨ n = 1 ∨ n = 2 := by
                omega
              rcases h₁₃ with (rfl | rfl | rfl) <;> simp [h₀, h₁, h₂, Nat.mod_eq_of_lt] <;> norm_num
              <;> try omega
          exact h₁₂
        have h₁₁ : n % 7 = 6 → d n % 2 = 1 := by
          intro h₁₁
          have h₁₂ : n % 7 = 6 := h₁₁
          have h₁₃ : d n % 2 = 1 := by
            by_cases h₁₄ : n ≥ 3
            · have h₁₅ : d n = d (n - 1) + d (n - 3) := h₃ n h₁₄
              rw [h₁₅]
              have h₁₆ : (n - 1) % 7 = 5 := by
                have h₁₇ : n % 7 = 6 := h₁₂
                omega
              have h₁₇ : (n - 3) % 7 = 3 := by
                have h₁₈ : n % 7 = 6 := h₁₂
                omega
              have h₁₈ : d (n - 1) % 2 = 0 := by
                have h₁₉ := ih ((n - 1)) (by
                  have h₂₀ : n - 1 < n := by
                    omega
                  omega)
                have h₂₀ := h₁₉.2.2.2.2.2.1 (by omega)
                omega
              have h₁₉ : d (n - 3) % 2 = 1 := by
                have h₂₀ := ih ((n - 3)) (by
                  have h₂₁ : n - 3 < n := by
                    omega
                  omega)
                have h₂₁ := h₂₀.2.2.2.1 (by omega)
                omega
              omega
            · have h₁₄ : n = 0 ∨ n = 1 ∨ n = 2 := by
                omega
              rcases h₁₄ with (rfl | rfl | rfl) <;> simp [h₀, h₁, h₂, Nat.mod_eq_of_lt] <;> norm_num
              <;> try omega
          exact h₁₃
        exact ⟨h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩
    exact h₄₁
  have h₅ : Even (d 2021) := by
    have h₅₁ := h₄ 2021
    have h₅₂ : 2021 % 7 = 5 := by norm_num
    have h₅₃ : d 2021 % 2 = 0 := by
      have h₅₄ := h₅₁.2.2.2.2.2.1
      have h₅₅ := h₅₄
      have h₅₆ := h₅₅ (by omega)
      omega
    have h₅₄ : Even (d 2021) := by
      rw [even_iff_two_dvd]
      omega
    exact h₅₄
  have h₆ : Odd (d 2022) := by
    have h₆₁ := h₄ 2022
    have h₆₂ : 2022 % 7 = 6 := by norm_num
    have h₆₃ : d 2022 % 2 = 1 := by
      have h₆₄ := h₆₁.2.2.2.2.2.2
      have h₆₅ := h₆₄
      have h₆₆ := h₆₅ (by omega)
      omega
    have h₆₄ : Odd (d 2022) := by
      rw [Nat.odd_iff_not_even]
      rw [even_iff_two_dvd]
      omega
    exact h₆₄
  have h₇ : Even (d 2023) := by
    have h₇₁ := h₄ 2023
    have h₇₂ : 2023 % 7 = 0 := by norm_num
    have h₇₃ : d 2023 % 2 = 0 := by
      have h₇₄ := h₇₁.1
      have h₇₅ := h₇₄
      have h₇₆ := h₇₅ (by omega)
      omega
    have h₇₄ : Even (d 2023) := by
      rw [even_iff_two_dvd]
      omega
    exact h₇₄
  exact ⟨h₅, h₆, h₇⟩