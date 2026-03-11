import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1987_p8 :
  IsGreatest { n : ℕ | 0 < n ∧ ∃! k : ℕ, (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13 } 112 := by
  have h_mem : 112 ∈ { n : ℕ | 0 < n ∧ ∃! k : ℕ, (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13 } := by
    constructor
    · norm_num
    use 97
    constructor
    · norm_num [div_lt_div_iff]
    intro k hk
    have h₁ := hk.1
    have h₂ := hk.2
    field_simp [add_comm] at h₁ h₂
    rw [← sub_pos] at h₁ h₂
    field_simp [add_comm] at h₁ h₂
    norm_cast at h₁ h₂
    ring_nf at h₁ h₂
    omega
  have h_bounds : ∀ (n k : ℕ), (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13 ↔ 
                   (6 : ℝ) * n / 7 < k ∧ k < (7 : ℝ) * n / 8 := by
    norm_num
    have h1 : ∀ n k : ℕ, (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13 ↔ (6 : ℝ) * n / 7 < k ∧ k < (7 : ℝ) * n / 8 := by
      intro n k
      constructor
      · intro h
        have h2 : (8 : ℝ) / 15 < n / (n + k) := h.1
        have h3 : (n : ℝ) / (n + k) < 7 / 13 := h.2
        constructor
        · have h4 : (0 : ℝ) < n + k := by
            by_contra h5
            have h6 : (n : ℝ) ≤ 0 := by linarith
            have h7 : (n : ℝ) / (n + k) ≤ 0 := by exact div_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
            have h8 : (8 : ℝ) / 15 < 0 := by linarith
            linarith
          field_simp at h2 h3
          rw [← sub_pos] at h2 h3
          field_simp at h2 h3
          rw [← sub_pos]
          field_simp
          ring_nf
          nlinarith
        · have h4 : (0 : ℝ) < n + k := by
            by_contra h5
            have h6 : (n : ℝ) ≤ 0 := by linarith
            have h7 : (n : ℝ) / (n + k) ≤ 0 := by exact div_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
            have h8 : (8 : ℝ) / 15 < 0 := by linarith
            linarith
          field_simp at h2 h3
          rw [← sub_pos] at h2 h3
          field_simp at h2 h3
          rw [← sub_pos]
          field_simp
          ring_nf
          nlinarith
      · intro h
        have h2 : (6 : ℝ) * n / 7 < k := h.1
        have h3 : k < (7 : ℝ) * n / 8 := h.2
        constructor
        · have h4 : (0 : ℝ) < n + k := by
            by_contra h5
            have h6 : (n : ℝ) ≤ 0 := by linarith
            have h7 : (6 : ℝ) * n / 7 ≤ 0 := by exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
            linarith
          field_simp at h2 h3 ⊢
          rw [← sub_pos] at h2 h3
          field_simp at h2 h3 ⊢
          rw [← sub_pos]
          field_simp
          ring_nf
          nlinarith
        · have h4 : (0 : ℝ) < n + k := by
            by_contra h5
            have h6 : (n : ℝ) ≤ 0 := by linarith
            have h7 : (7 : ℝ) * n / 8 ≤ 0 := by exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
            linarith
          field_simp at h2 h3 ⊢
          rw [← sub_pos] at h2 h3
          field_simp at h2 h3 ⊢
          rw [← sub_pos]
          field_simp
          ring_nf
          nlinarith
    intro n k
    simp_all
  have h_interval_length : ∀ n : ℕ, (7 : ℝ) * n / 8 - (6 : ℝ) * n / 7 = n / 56 := by
    intro n
    have h := h_bounds 112 0
    have h₁ := h_bounds 0 0
    have h₂ := h_bounds 16 0
    have h₃ := h_bounds 1 0
    have h₄ := h_bounds 0 1
    have h₅ := h_bounds 1 1
    have h₆ := h_bounds 0 1
    have h₇ := h_bounds 16 1
    norm_num at h h₁ h₂ h₃ h₄ h₅ h₆ h₇
    <;> linarith
  
  have h_at_most_one : ∀ n : ℕ, n ≥ 113 → ∃ k₁ k₂ : ℕ, k₁ ≠ k₂ ∧ 
                       (6 : ℝ) * n / 7 < k₁ ∧ k₁ < (7 : ℝ) * n / 8 ∧
                       (6 : ℝ) * n / 7 < k₂ ∧ k₂ < (7 : ℝ) * n / 8 := by
    intro n hn
    norm_num [h_bounds, h_interval_length] at *
    use 6 * n / 7 + 1, 6 * n / 7 + 2
    constructor
    <;> norm_num [div_lt_iff, lt_div_iff] at *
    <;> ring_nf at *
    <;> norm_cast at *
    <;> omega
  have h_n112_unique_k : ∃! k : ℕ, (8 : ℝ) / 15 < 112 / (112 + k) ∧ (112 : ℝ) / (112 + k) < 7 / 13 := by
    have h₁ := h_bounds 112 0
    have h₂ := h_bounds 112 1
    have h₃ := h_bounds 112 2
    have h₄ := h_bounds 112 3
    have h₅ := h_bounds 112 4
    have h₆ := h_bounds 112 5
    have h₇ := h_bounds 112 6
    have h₈ := h_bounds 112 7
    have h₉ := h_bounds 112 8
    have h₁₀ := h_bounds 112 9
    have h₁₁ := h_bounds 112 10
    have h₁₂ := h_bounds 112 11
    have h₁₃ := h_bounds 112 12
    have h₁₄ := h_bounds 112 13
    have h₁₅ := h_bounds 112 14
    have h₁₆ := h_bounds 112 15
    have h₁₇ := h_bounds 112 16
    have h₁₈ := h_bounds 112 17
    have h₁₉ := h_bounds 112 18
    have h₂₀ := h_bounds 112 19
    have h₂₁ := h_bounds 112 20
    have h₂₂ := h_bounds 112 21
    have h₂₃ := h_bounds 112 22
    have h₂₄ := h_bounds 112 23
    have h₂₅ := h_bounds 112 24
    have h₂₆ := h_bounds 112 25
    have h₂₇ := h_bounds 112 26
    have h₂₈ := h_bounds 112 27
    have h₂₉ := h_bounds 112 28
    have h₃₀ := h_bounds 112 29
    have h₃₁ := h_bounds 112 30
    have h₃₂ := h_bounds 112 31
    have h₃₃ := h_bounds 112 32
    have h₃₄ := h_bounds 112 33
    have h₃₅ := h_bounds 112 34
    have h₃₆ := h_bounds 112 35
    have h₃₇ := h_bounds 112 36
    have h₃₈ := h_bounds 112 37
    have h₃₉ := h_bounds 112 38
    have h₄₀ := h_bounds 112 39
    have h₄₁ := h_bounds 112 40
    have h₄₂ := h_bounds 112 41
    have h₄₃ := h_bounds 112 42
    have h₄₄ := h_bounds 112 43
    have h₄₅ := h_bounds 112 44
    have h₄₆ := h_bounds 112 45
    have h₄₇ := h_bounds 112 46
    have h₄₈ := h_bounds 112 47
    have h₄₉ := h_bounds 112 48
    have h₅₀ := h_bounds 112 49
    have h₅₁ := h_bounds 112 50
    have h₅₂ := h_bounds 112 51
    have h₅₃ := h_bounds 112 52
    have h₅₄ := h_bounds 112 53
    have h₅₅ := h_bounds 112 54
    have h₅₆ := h_bounds 112 55
    have h₅₇ := h_bounds 112 56
    have h₅₈ := h_bounds 112 57
    have h₅₉ := h_bounds 112 58
    have h₆₀ := h_bounds 112 59
    have h₆₁ := h_bounds 112 60
    have h₆₂ := h_bounds 112 61
    have h₆₃ := h_bounds 112 62
    have h₆₄ := h_bounds 112 63
    have h₆₅ := h_bounds 112 64
    have h₆₆ := h_bounds 112 65
    have h₆₇ := h_bounds 112 66
    have h₆₈ := h_bounds 112 67
    have h₆₉ := h_bounds 112 68
    have h₇₀ := h_bounds 112 69
    have h₇₁ := h_bounds 112 70
    have h₇₂ := h_bounds 112 71
    have h₇₃ := h_bounds 112 72
    have h₇₄ := h_bounds 112 73
    have h₇₅ := h_bounds 112 74
    have h₇₆ := h_bounds 112 75
    have h₇₇ := h_bounds 112 76
    have h₇₈ := h_bounds 112 77
    have h₇₉ := h_bounds 112 78
    have h₈₀ := h_bounds 112 79
    have h₈₁ := h_bounds 112 80
    have h₈₂ := h_bounds 112 81
    have h₈₃ := h_bounds 112 82
    have h₈₄ := h_bounds 112 83
    have h₈₅ := h_bounds 112 84
    have h₈₆ := h_bounds 112 85
    have h₈₇ := h_bounds 112 86
    have h₈₈ := h_bounds 112 87
    have h₈₉ := h_bounds 112 88
    have h₉₀ := h_bounds 112 89
    have h₉₁ := h_bounds 112 90
    have h₉₂ := h_bounds 112 91
    have h₉₃ := h_bounds 112 92
    have h₉₄ := h_bounds 112 93
    have h₉₅ := h_bounds 112 94
    have h₉₆ := h_bounds 112 95
    have h₉₇ := h_bounds 112 96
    have h₉₈ := h_bounds 112 97
    have h₉₉ := h_bounds 112 98
    have h₁₀₀ := h_bounds 112 99
    have h₁₀₁ := h_bounds 112 100
    -- Normalize the expressions to simplify the proof
    norm_num at *
    -- Use the given conditions to find the unique k such that 8/15 < 112 / (112 + k) < 7 / 13
    <;> simp_all [h_at_most_one]
    <;> norm_num
    <;> linarith
  
  have h_n112_k_is_97 : (8 : ℝ) / 15 < 112 / (112 + 97) ∧ (112 : ℝ) / (112 + 97) < 7 / 13 := by
    have h₁ := h_bounds 112 97
    have h₂ := h_interval_length 112
    have h₃ := h_at_most_one 112
    have h₄ := h_n112_unique_k
    norm_num at h₁ h₂ h₃ h₄
    <;> simp_all [div_lt_div_iff]
    <;> norm_num
    <;> linarith
  
  have h_greatest : ∀ n : ℕ, n ∈ { n : ℕ | 0 < n ∧ ∃! k : ℕ, (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13 } → n ≤ 112 := by
    intro n hn
    have hn' := hn
    simp only [Set.mem_setOf_eq] at hn'
    have hn'' := hn'
    cases' hn'' with hn_pos hn_unique
    have hn_le_112 : n ≤ 112 := by
      by_contra h
      have h' : n ≥ 113 := by linarith
      have h'' := h_at_most_one n h'
      obtain ⟨k₁, k₂, h_k₁_k₂, h_k₁_ineq, h_k₂_ineq⟩ := h''
      have h_k₁_eq_k₂ : k₁ = k₂ := by
        apply ExistsUnique.unique hn_unique
        <;> aesop
      aesop
    exact hn_le_112
  refine' ⟨by simpa [h_mem] using h_greatest 112, fun a ha => _⟩
  have h₁ := h_bounds 0 0
  have h₂ := h_bounds 0 1
  have h₃ := h_bounds 1 0
  have h₄ := h_bounds 1 1
  have h₅ := h_bounds 2 1
  have h₆ := h_bounds 3 1
  have h₇ := h_bounds 4 1
  have h₈ := h_bounds 5 2
  have h₉ := h_bounds 6 2
  have h₁₀ := h_bounds 7 3
  have h₁₁ := h_bounds 8 3
  have h₁₂ := h_bounds 9 4
  have h₁₃ := h_bounds 10 4
  have h₁₄ := h_bounds 11 5
  have h₁₅ := h_bounds 12 6
  have h₁₆ := h_bounds 13 7
  have h₁₇ := h_bounds 14 8
  have h₁₈ := h_bounds 15 9
  have h₁₉ := h_bounds 16 10
  have h₂₀ := h_bounds 17 11
  have h₂₁ := h_bounds 18 12
  have h₂₂ := h_bounds 19 13
  have h₂₃ := h_bounds 20 14
  have h₂₄ := h_bounds 21 15
  have h₂₅ := h_bounds 22 16
  have h₂₆ := h_bounds 23 17
  have h₂₇ := h_bounds 24 19
  have h₂₈ := h_bounds 25 20
  have h₂₉ := h_bounds 26 21
  have h₃₀ := h_bounds 27 22
  have h₃₁ := h_bounds 28 23
  have h₃₂ := h_bounds 29 24
  have h₃₃ := h_bounds 30 26
  have h₃₄ := h_bounds 31 27
  have h₃₅ := h_bounds 32 29
  have h₃₆ := h_bounds 33 30
  have h₃₇ := h_bounds 34 31
  have h₃₈ := h_bounds 35 33
  have h₃₉ := h_bounds 36 34
  have h₄₀ := h_bounds 37 35
  have h₄₁ := h_bounds 38 37
  have h₄₂ := h_bounds 39 38
  have h₄₃ := h_bounds 40 40
  have h₄₄ := h_bounds 41 41
  have h₄₅ := h_bounds 42 43
  have h₄₆ := h_bounds 43 44
  have h₄₇ := h_bounds 44 46
  have h₄₈ := h_bounds 45 47
  have h₄₉ := h_bounds 46 49
  have h₅₀ := h_bounds 47 51
  have h₅₁ := h_bounds 48 52
  have h₅₂ := h_bounds 49 54
  have h₅₃ := h_bounds 50 56
  have h₅₄ := h_bounds 51 58
  have h₅₅ := h_bounds 52 60
  have h₅₆ := h_bounds 53 62
  have h₅₇ := h_bounds 54 64
  have h₅₈ := h_bounds 55 66
  have h₅₉ := h_bounds 56 68
  have h₆₀ := h_bounds 57 71
  have h₆₁ := h_bounds 58 73
  have h₆₂ := h_bounds 59 75
  have h₆₃ := h_bounds 60 78
  have h₆₄ := h_bounds 61 80
  have h₆₅ := h_bounds 62 83
  have h₆₆ := h_bounds 63 85
  have h₆₇ := h_bounds 64 88
  have h₆₈ := h_bounds 65 91
  have h₆₉ := h_bounds 66 94
  have h₇₀ := h_bounds 67 97
  have h₇₁ := h_bounds 68 100
  have h₇₂ := h_bounds 69 103
  have h₇₃ := h_bounds 70 107
  have h₇₄ := h_bounds 71 110
  have h₇₅ := h_bounds 72 114
  have h₇₆ := h_bounds 73 118
  have h₇₇ := h_bounds 74 122
  have h₇₈ := h_bounds 75 126
  have h₇₉ := h_bounds 76 131
  have h₈₀ := h_bounds 77 135
  have h₈₁ := h_bounds 78 140
  have h₈₂ := h_bounds 79 145
  have h₈₃ := h_bounds 80 150
  have h₈₄ := h_bounds 81 155
  have h₈₅ := h_bounds 82 161
  have h₈₆ := h_bounds 83 166
  have h₈₇ := h_bounds 84 172
  have h₈₈ := h_bounds 85 178
  have h₈₉ := h_bounds 86 184
  have h₉₀ := h_bounds 87 190
  have h₉₁ := h_bounds 88 197
  have h₉₂ := h_bounds 89 203
  have h₉₃ := h_bounds 90 210
  have h₉₄ := h_bounds 91 217
  have h₉₅ := h_bounds 92 224
  have h₉₆ := h_bounds 93 232
  have h₉₇ := h_bounds 94 239
  have h₉₈ := h_bounds 95 247
  have h₉₉ := h_bounds 96 255
  have h₁₀₀ := h_bounds 97 263
  have h₁₀₁ := h_bounds 98 271
  have h₁₀₂ := h_bounds 99 280
  have h₁₀₃ := h_bounds 100 288
  norm_num at ha
  <;> simp_all
  <;> norm_num
  <;> linarith