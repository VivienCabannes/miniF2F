import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2020_p21
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n)) :
  S.card = 6 := by
  have h_main : S = {400, 470, 2290, 2360, 2430, 2500} := by
    apply Finset.ext
    intro n
    rw [h₀]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · -- Prove the forward direction: if n ∈ S, then n is one of the six values
      intro h
      have h₁ : 0 < n := h.1
      have h₂ : (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n) := h.2
      have h₃ : (n + 1000) % 70 = 0 := by
        have h₄ : ((n : ℝ) + 1000) / 70 = Int.floor (Real.sqrt n) := by exact_mod_cast h₂
        have h₅ : (n + 1000 : ℤ) % 70 = 0 := by
          have h₆ : ((n : ℝ) + 1000 : ℝ) / 70 = Int.floor (Real.sqrt n) := by exact_mod_cast h₂
          have h₇ : (n : ℤ) + 1000 ≡ 0 [ZMOD 70] := by
            have h₈ : ((n : ℝ) + 1000 : ℝ) / 70 = Int.floor (Real.sqrt n) := by exact_mod_cast h₂
            have h₉ : (Int.floor (Real.sqrt n) : ℝ) = ((n : ℝ) + 1000 : ℝ) / 70 := by linarith
            have h₁₀ : (Int.floor (Real.sqrt n) : ℝ) * 70 = (n : ℝ) + 1000 := by linarith
            have h₁₁ : (Int.floor (Real.sqrt n) : ℤ) * 70 = (n : ℤ) + 1000 := by
              norm_cast at h₁₀ ⊢
              <;> (try norm_num at h₁₀ ⊢) <;> (try ring_nf at h₁₀ ⊢) <;> (try field_simp at h₁₀ ⊢) <;> (try norm_cast at h₁₀ ⊢) <;> (try linarith)
              <;> (try ring_nf at h₁₀ ⊢) <;> (try norm_cast at h₁₀ ⊢) <;> (try linarith)
            have h₁₂ : (n : ℤ) + 1000 ≡ 0 [ZMOD 70] := by
              rw [Int.ModEq]
              omega
            exact h₁₂
          exact h₇
        exact_mod_cast h₅
      have h₄ : n % 70 = 50 := by
        omega
      have h₅ : ∃ k : ℕ, n = 70 * k + 50 := by
        use n / 70
        have h₆ := Nat.mod_add_div n 70
        omega
      obtain ⟨k, h₆⟩ := h₅
      have h₇ : k + 15 = Int.floor (Real.sqrt n) := by
        have h₈ : ((n : ℝ) + 1000 : ℝ) / 70 = Int.floor (Real.sqrt n) := by exact_mod_cast h₂
        have h₉ : (k : ℝ) + 15 = ((n : ℝ) + 1000 : ℝ) / 70 := by
          rw [h₆]
          <;> ring_nf at *
          <;> norm_num
          <;> field_simp at *
          <;> ring_nf at *
          <;> norm_cast at *
          <;> linarith
        have h₁₀ : (k : ℝ) + 15 = (Int.floor (Real.sqrt n) : ℝ) := by
          linarith
        have h₁₁ : (k : ℤ) + 15 = Int.floor (Real.sqrt n) := by
          norm_cast at h₁₀ ⊢
          <;> (try norm_num at h₁₀ ⊢) <;> (try ring_nf at h₁₀ ⊢) <;> (try field_simp at h₁₀ ⊢) <;> (try norm_cast at h₁₀ ⊢) <;> (try linarith)
        exact_mod_cast h₁₁
      have h₈ : (k + 15 : ℝ) ^ 2 ≤ (n : ℝ) := by
        have h₉ : (k + 15 : ℝ) ≤ Real.sqrt n := by
          have h₁₀ : (k + 15 : ℝ) ≤ Real.sqrt n := by
            have h₁₁ : (k + 15 : ℝ) = Int.floor (Real.sqrt n) := by
              exact_mod_cast h₇
            have h₁₂ : (Int.floor (Real.sqrt n) : ℝ) ≤ Real.sqrt n := by
              exact Int.floor_le (Real.sqrt n)
            linarith
          exact h₁₀
        have h₁₀ : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
        have h₁₁ : (k + 15 : ℝ) ^ 2 ≤ (n : ℝ) := by
          nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)), h₉]
        exact h₁₁
      have h₉ : (n : ℝ) < (k + 16 : ℝ) ^ 2 := by
        have h₁₀ : Real.sqrt n < (k + 16 : ℝ) := by
          have h₁₁ : Real.sqrt n < (k + 16 : ℝ) := by
            have h₁₂ : (Int.floor (Real.sqrt n) : ℝ) = (k + 15 : ℝ) := by
              have h₁₃ : (k + 15 : ℝ) = Int.floor (Real.sqrt n) := by
                exact_mod_cast h₇
              linarith
            have h₁₃ : Real.sqrt n < (Int.floor (Real.sqrt n) : ℝ) + 1 := by
              linarith [Int.floor_le (Real.sqrt n), Int.lt_floor_add_one (Real.sqrt n)]
            linarith
          exact h₁₁
        have h₁₁ : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
        have h₁₂ : (n : ℝ) < (k + 16 : ℝ) ^ 2 := by
          nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)), h₁₀]
        exact h₁₂
      have h₁₀ : (k + 15 : ℕ) ^ 2 ≤ n := by
        norm_cast at h₈ ⊢
        <;> (try ring_nf at h₈ ⊢) <;> (try norm_num at h₈ ⊢) <;> (try nlinarith)
      have h₁₁ : n < (k + 16 : ℕ) ^ 2 := by
        norm_cast at h₉ ⊢
        <;> (try ring_nf at h₉ ⊢) <;> (try norm_num at h₉ ⊢) <;> (try nlinarith)
      have h₁₂ : k ≤ 35 := by
        by_contra h
        have h₁₃ : k ≥ 36 := by omega
        have h₁₄ : (k + 15 : ℕ) ^ 2 > n := by
          nlinarith
        nlinarith
      have h₁₃ : k ≥ 5 ∨ k ≤ 4 := by omega
      cases h₁₃ with
      | inl h₁₄ =>
        have h₁₅ : k ≥ 5 := h₁₄
        have h₁₆ : k ≤ 35 := by omega
        interval_cases k <;> norm_num at h₆ h₁₀ h₁₁ h₈ h₉ h₇ ⊢ <;>
          (try omega) <;>
          (try
            {
              have h₁₇ : n = 400 := by omega
              simp_all [h₁₇]
              <;> norm_num [Int.emod_eq_of_lt] at *
              <;>
                (try
                  {
                    rw [eq_comm]
                    <;> norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt]
                    <;>
                      (try
                        {
                          constructor <;> norm_num <;>
                            nlinarith [Real.sqrt_nonneg 400, Real.sq_sqrt (show 0 ≤ (400 : ℝ) by norm_num)]
                        })
                  })
            }) <;>
          (try
            {
              have h₁₇ : n = 470 := by omega
              simp_all [h₁₇]
              <;> norm_num [Int.emod_eq_of_lt] at *
              <;>
                (try
                  {
                    rw [eq_comm]
                    <;> norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt]
                    <;>
                      (try
                        {
                          constructor <;> norm_num <;>
                            nlinarith [Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num)]
                        })
                  })
            }) <;>
          (try
            {
              have h₁₇ : n = 2290 := by omega
              simp_all [h₁₇]
              <;> norm_num [Int.emod_eq_of_lt] at *
              <;>
                (try
                  {
                    rw [eq_comm]
                    <;> norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt]
                    <;>
                      (try
                        {
                          constructor <;> norm_num <;>
                            nlinarith [Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num)]
                        })
                  })
            }) <;>
          (try
            {
              have h₁₇ : n = 2360 := by omega
              simp_all [h₁₇]
              <;> norm_num [Int.emod_eq_of_lt] at *
              <;>
                (try
                  {
                    rw [eq_comm]
                    <;> norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt]
                    <;>
                      (try
                        {
                          constructor <;> norm_num <;>
                            nlinarith [Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num)]
                        })
                  })
            }) <;>
          (try
            {
              have h₁₇ : n = 2430 := by omega
              simp_all [h₁₇]
              <;> norm_num [Int.emod_eq_of_lt] at *
              <;>
                (try
                  {
                    rw [eq_comm]
                    <;> norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt]
                    <;>
                      (try
                        {
                          constructor <;> norm_num <;>
                            nlinarith [Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num)]
                        })
                  })
            }) <;>
          (try
            {
              have h₁₇ : n = 2500 := by omega
              simp_all [h₁₇]
              <;> norm_num [Int.emod_eq_of_lt] at *
              <;>
                (try
                  {
                    rw [eq_comm]
                    <;> norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt]
                    <;>
                      (try
                        {
                          constructor <;> norm_num <;>
                            nlinarith [Real.sqrt_nonneg 2500, Real.sq_sqrt (show 0 ≤ (2500 : ℝ) by norm_num)]
                        })
                  })
            }) <;>
          (try omega)
      | inr h₁₄ =>
        have h₁₅ : k ≤ 4 := h₁₄
        have h₁₆ : k ≥ 0 := by omega
        interval_cases k <;> norm_num at h₆ h₁₀ h₁₁ h₈ h₉ h₇ ⊢ <;>
          (try omega) <;>
          (try
            {
              have h₁₇ : n = 400 := by omega
              simp_all [h₁₇]
              <;> norm_num [Int.emod_eq_of_lt] at *
              <;>
                (try
                  {
                    rw [eq_comm]
                    <;> norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt]
                    <;>
                      (try
                        {
                          constructor <;> norm_num <;>
                            nlinarith [Real.sqrt_nonneg 400, Real.sq_sqrt (show 0 ≤ (400 : ℝ) by norm_num)]
                        })
                  })
            }) <;>
          (try omega)
    · -- Prove the reverse direction: if n is one of the six values, then n ∈ S
      intro h
      have h₁ : n = 400 ∨ n = 470 ∨ n = 2290 ∨ n = 2360 ∨ n = 2430 ∨ n = 2500 := by
        tauto
      rcases h₁ with (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Case n = 400
        constructor
        · -- Prove 0 < 400
          norm_num
        · -- Prove (↑400 + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 400)
          have h₂ : Int.floor (Real.sqrt 400 : ℝ) = 20 := by
            rw [Int.floor_eq_iff]
            constructor
            · -- Prove 20 ≤ Real.sqrt 400
              norm_num [Real.le_sqrt, Real.sqrt_lt]
            · -- Prove Real.sqrt 400 < 20 + 1
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 400, Real.sq_sqrt (show 0 ≤ (400 : ℝ) by norm_num)]
          norm_num [h₂]
          <;>
          nlinarith [Real.sqrt_nonneg 400, Real.sq_sqrt (show 0 ≤ (400 : ℝ) by norm_num)]
      · -- Case n = 470
        constructor
        · -- Prove 0 < 470
          norm_num
        · -- Prove (↑470 + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 470)
          have h₂ : Int.floor (Real.sqrt 470 : ℝ) = 21 := by
            rw [Int.floor_eq_iff]
            constructor
            · -- Prove 21 ≤ Real.sqrt 470
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num),
                Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num)]
            · -- Prove Real.sqrt 470 < 21 + 1
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num),
                Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num)]
          norm_num [h₂]
          <;>
          nlinarith [Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num)]
      · -- Case n = 2290
        constructor
        · -- Prove 0 < 2290
          norm_num
        · -- Prove (↑2290 + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2290)
          have h₂ : Int.floor (Real.sqrt 2290 : ℝ) = 47 := by
            rw [Int.floor_eq_iff]
            constructor
            · -- Prove 47 ≤ Real.sqrt 2290
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num),
                Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num)]
            · -- Prove Real.sqrt 2290 < 47 + 1
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num),
                Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num)]
          norm_num [h₂]
          <;>
          nlinarith [Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num)]
      · -- Case n = 2360
        constructor
        · -- Prove 0 < 2360
          norm_num
        · -- Prove (↑2360 + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2360)
          have h₂ : Int.floor (Real.sqrt 2360 : ℝ) = 48 := by
            rw [Int.floor_eq_iff]
            constructor
            · -- Prove 48 ≤ Real.sqrt 2360
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num),
                Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num)]
            · -- Prove Real.sqrt 2360 < 48 + 1
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num),
                Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num)]
          norm_num [h₂]
          <;>
          nlinarith [Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num)]
      · -- Case n = 2430
        constructor
        · -- Prove 0 < 2430
          norm_num
        · -- Prove (↑2430 + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2430)
          have h₂ : Int.floor (Real.sqrt 2430 : ℝ) = 49 := by
            rw [Int.floor_eq_iff]
            constructor
            · -- Prove 49 ≤ Real.sqrt 2430
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num),
                Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num)]
            · -- Prove Real.sqrt 2430 < 49 + 1
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num),
                Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num)]
          norm_num [h₂]
          <;>
          nlinarith [Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num)]
      · -- Case n = 2500
        constructor
        · -- Prove 0 < 2500
          norm_num
        · -- Prove (↑2500 + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2500)
          have h₂ : Int.floor (Real.sqrt 2500 : ℝ) = 50 := by
            rw [Int.floor_eq_iff]
            constructor
            · -- Prove 50 ≤ Real.sqrt 2500
              norm_num [Real.le_sqrt, Real.sqrt_lt]
            · -- Prove Real.sqrt 2500 < 50 + 1
              norm_num [Real.le_sqrt, Real.sqrt_lt]
              <;>
              nlinarith [Real.sqrt_nonneg 2500, Real.sq_sqrt (show 0 ≤ (2500 : ℝ) by norm_num)]
          norm_num [h₂]
          <;>
          nlinarith [Real.sqrt_nonneg 2500, Real.sq_sqrt (show 0 ≤ (2500 : ℝ) by norm_num)]
  
  have h_card : S.card = 6 := by
    rw [h_main]
    norm_num
    <;> rfl
  
  exact h_card