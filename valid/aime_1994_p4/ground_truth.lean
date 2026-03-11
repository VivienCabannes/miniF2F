import Mathlib
import Aesop
set_option maxHeartbeats 400000
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat

lemma round6_h_logb_nonneg (x : ℕ) (hx : x ≥ 1) : 0 ≤ Int.floor (Real.logb 2 (x : ℝ)) := by
  have h₁ : (x : ℝ) ≥ 1 := by exact_mod_cast hx
  have h₂ : Real.logb 2 (x : ℝ) ≥ 0 := by
    have h₃ : Real.logb 2 (x : ℝ) = Real.log (x : ℝ) / Real.log 2 := by
      rw [Real.logb]
    rw [h₃]
    have h₄ : Real.log (x : ℝ) ≥ 0 := by
      apply Real.log_nonneg
      linarith
    have h₅ : Real.log 2 > 0 := by
      apply Real.log_pos
      norm_num
    have h₆ : Real.log (x : ℝ) / Real.log 2 ≥ 0 := div_nonneg h₄ (by linarith)
    linarith
  have h₃ : Int.floor (Real.logb 2 (x : ℝ)) ≥ 0 := by
    apply Int.floor_nonneg.mpr
    linarith
  exact h₃


lemma round9_sum_split_7cc0bfa2 (f : ℕ → ℤ) (a b c : ℕ) (h₁ : a ≤ c) (h₂ : c < b) :
  ∑ k in Finset.Icc a b, f k = (∑ k in Finset.Icc a c, f k) + ∑ k in Finset.Icc (c + 1) b, f k := by
  have h₃ : a ≤ b := by linarith
  have h₄ : c + 1 ≤ b := by linarith
  have h₅ : Finset.Icc a b = Finset.Icc a c ∪ Finset.Icc (c + 1) b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨hax, hxb⟩
      by_cases h : x ≤ c
      · exact Or.inl ⟨hax, h⟩
      · have h' : c + 1 ≤ x := by omega
        exact Or.inr ⟨h', hxb⟩
    · rintro (h | h)
      · exact ⟨h.1, by linarith⟩
      · exact ⟨by linarith, h.2⟩
  have h₆ : Disjoint (Finset.Icc a c) (Finset.Icc (c + 1) b) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Finset.mem_Icc] at hx₁ hx₂
    linarith
  rw [h₅, Finset.sum_union h₆]


lemma round10_sum_1_1_7cc0c538 : (∑ k : ℕ in Finset.Icc 1 1, Int.floor (Real.logb 2 (k : ℝ))) = 0 := by
  norm_num


lemma round12_log2_pos_7cc0c9f2 : 0 < Real.log 2 := by
  have h₁ : Real.log 2 > Real.log 1 := Real.log_lt_log (by norm_num) (by norm_num)
  have h₂ : Real.log 1 = 0 := Real.log_one
  linarith


lemma round12_floor_logb_interval_7cc0ce84 (n : ℕ) (k : ℕ) (hk1 : 2^n ≤ k) (hk2 : k < 2^(n+1)) :
    Int.floor (Real.logb 2 (k : ℝ)) = (n : ℤ) := by
  have h1 : (k : ℝ) > 0 := by
    have h1' : k ≥ 1 := by
      calc
        k ≥ 2 ^ n := hk1
        _ ≥ 2 ^ 0 := by apply Nat.pow_le_pow_right; norm_num; linarith
        _ = 1 := by norm_num
    have h1'' : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h1'
    linarith
  have h2 : (2 : ℝ) > 0 := by norm_num
  have h3 : (2 : ℝ) ≠ 1 := by norm_num
  have h4 : Real.log 2 > 0 := round12_log2_pos_7cc0c9f2
  have h5 : (2 ^ n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have h6 : (k : ℝ) < (2 ^ (n + 1) : ℝ) := by exact_mod_cast hk2
  have h7 : Real.log (2 ^ n) ≤ Real.log (k : ℝ) := Real.log_le_log (by positivity) h5
  have h8 : Real.log (k : ℝ) < Real.log (2 ^ (n + 1)) := Real.log_lt_log (by positivity) h6
  have h9 : Real.log (2 ^ n) = (n : ℝ) * Real.log 2 := by
    simp [Real.log_pow]
    <;> ring
  have h10 : Real.log (2 ^ (n + 1)) = ((n : ℝ) + 1) * Real.log 2 := by
    simp [Real.log_pow]
    <;> ring
  have h11 : (n : ℝ) * Real.log 2 ≤ Real.log (k : ℝ) := by linarith [h7, h9]
  have h12 : Real.log (k : ℝ) < ((n : ℝ) + 1) * Real.log 2 := by linarith [h8, h10]
  have h13 : (n : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 := by
    have h14 : 0 < Real.log 2 := round12_log2_pos_7cc0c9f2
    have h15 : (n : ℝ) * Real.log 2 ≤ Real.log (k : ℝ) := h11
    have h16 : Real.log (k : ℝ) / Real.log 2 - (n : ℝ) = (Real.log (k : ℝ) - (n : ℝ) * Real.log 2) / Real.log 2 := by
      field_simp [h14.ne'] <;> ring
    have h17 : Real.log (k : ℝ) - (n : ℝ) * Real.log 2 ≥ 0 := by linarith
    have h18 : (Real.log (k : ℝ) - (n : ℝ) * Real.log 2) / Real.log 2 ≥ 0 := div_nonneg h17 (by linarith)
    have h19 : Real.log (k : ℝ) / Real.log 2 - (n : ℝ) ≥ 0 := by linarith [h16, h18]
    have h20 : Real.log (k : ℝ) / Real.log 2 ≥ (n : ℝ) := by linarith
    exact h20
  have h14 : Real.log (k : ℝ) / Real.log 2 < (n : ℝ) + 1 := by
    have h15 : 0 < Real.log 2 := round12_log2_pos_7cc0c9f2
    have h16 : Real.log (k : ℝ) < ((n : ℝ) + 1) * Real.log 2 := h12
    have h17 : Real.log (k : ℝ) / Real.log 2 - ((n : ℝ) + 1) = (Real.log (k : ℝ) - ((n : ℝ) + 1) * Real.log 2) / Real.log 2 := by
      field_simp [h15.ne'] <;> ring
    have h18 : Real.log (k : ℝ) - ((n : ℝ) + 1) * Real.log 2 < 0 := by linarith
    have h19 : (Real.log (k : ℝ) - ((n : ℝ) + 1) * Real.log 2) / Real.log 2 < 0 := div_neg_of_neg_of_pos h18 h15
    have h20 : Real.log (k : ℝ) / Real.log 2 - ((n : ℝ) + 1) < 0 := by linarith [h17, h19]
    have h21 : Real.log (k : ℝ) / Real.log 2 < (n : ℝ) + 1 := by linarith
    exact h21
  have h15 : (n : ℝ) ≤ Real.logb 2 (k : ℝ) := by
    have h16 : Real.logb 2 (k : ℝ) = Real.log (k : ℝ) / Real.log 2 := by
      rw [Real.logb]
    rw [h16]
    exact h13
  have h16 : Real.logb 2 (k : ℝ) < (n : ℝ) + 1 := by
    have h17 : Real.logb 2 (k : ℝ) = Real.log (k : ℝ) / Real.log 2 := by
      rw [Real.logb]
    rw [h17]
    exact h14
  have h17 : Int.floor (Real.logb 2 (k : ℝ)) = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    norm_num at h15 h16 ⊢ <;> constructor <;> norm_num <;> linarith
  exact h17


lemma round10_sum_2_3_7cc0d4d8 : (∑ k : ℕ in Finset.Icc 2 3, Int.floor (Real.logb 2 (k : ℝ))) = 2 := by
  have h1 : ∀ k : ℕ, k ∈ Finset.Icc 2 3 → Int.floor (Real.logb 2 (k : ℝ)) = 1 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h2 : 2 ≤ k := hk.1
    have h3 : k ≤ 3 := hk.2
    have h4 : k < 2 ^ (1 + 1) := by omega
    have h5 : 2 ^ 1 ≤ k := by omega
    have h6 : Int.floor (Real.logb 2 (k : ℝ)) = 1 := round12_floor_logb_interval_7cc0ce84 1 k h5 h4
    exact h6
  have h2 : (∑ k : ℕ in Finset.Icc 2 3, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 2 3, 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  <;> norm_num


lemma round10_sum_4_7_7cc0d938 : (∑ k : ℕ in Finset.Icc 4 7, Int.floor (Real.logb 2 (k : ℝ))) = 8 := by
  have h1 : ∀ k : ℕ, k ∈ Finset.Icc 4 7 → Int.floor (Real.logb 2 (k : ℝ)) = 2 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h2 : 4 ≤ k := hk.1
    have h3 : k ≤ 7 := hk.2
    have h4 : k < 2 ^ (2 + 1) := by omega
    have h5 : 2 ^ 2 ≤ k := by omega
    have h6 : Int.floor (Real.logb 2 (k : ℝ)) = 2 := round12_floor_logb_interval_7cc0ce84 2 k h5 h4
    exact h6
  have h2 : (∑ k : ℕ in Finset.Icc 4 7, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 4 7, 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  <;> norm_num


lemma round10_sum_8_15_7cc0dd70 : (∑ k : ℕ in Finset.Icc 8 15, Int.floor (Real.logb 2 (k : ℝ))) = 24 := by
  have h1 : ∀ k : ℕ, k ∈ Finset.Icc 8 15 → Int.floor (Real.logb 2 (k : ℝ)) = 3 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h2 : 8 ≤ k := hk.1
    have h3 : k ≤ 15 := hk.2
    have h4 : k < 2 ^ (3 + 1) := by omega
    have h5 : 2 ^ 3 ≤ k := by omega
    have h6 : Int.floor (Real.logb 2 (k : ℝ)) = 3 := round12_floor_logb_interval_7cc0ce84 3 k h5 h4
    exact h6
  have h2 : (∑ k : ℕ in Finset.Icc 8 15, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 8 15, 3) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  <;> norm_num


lemma round10_sum_16_31_7cc0e1b2 : (∑ k : ℕ in Finset.Icc 16 31, Int.floor (Real.logb 2 (k : ℝ))) = 64 := by
  have h1 : ∀ k : ℕ, k ∈ Finset.Icc 16 31 → Int.floor (Real.logb 2 (k : ℝ)) = 4 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h2 : 16 ≤ k := hk.1
    have h3 : k ≤ 31 := hk.2
    have h4 : k < 2 ^ (4 + 1) := by omega
    have h5 : 2 ^ 4 ≤ k := by omega
    have h6 : Int.floor (Real.logb 2 (k : ℝ)) = 4 := round12_floor_logb_interval_7cc0ce84 4 k h5 h4
    exact h6
  have h2 : (∑ k : ℕ in Finset.Icc 16 31, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 16 31, 4) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  <;> norm_num


lemma round10_sum_32_63_7cc0e63a : (∑ k : ℕ in Finset.Icc 32 63, Int.floor (Real.logb 2 (k : ℝ))) = 160 := by
  have h1 : ∀ k : ℕ, k ∈ Finset.Icc 32 63 → Int.floor (Real.logb 2 (k : ℝ)) = 5 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h2 : 32 ≤ k := hk.1
    have h3 : k ≤ 63 := hk.2
    have h4 : k < 2 ^ (5 + 1) := by omega
    have h5 : 2 ^ 5 ≤ k := by omega
    have h6 : Int.floor (Real.logb 2 (k : ℝ)) = 5 := round12_floor_logb_interval_7cc0ce84 5 k h5 h4
    exact h6
  have h2 : (∑ k : ℕ in Finset.Icc 32 63, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 32 63, 5) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  <;> norm_num


lemma round10_sum_64_127_7cc0eb08 : (∑ k : ℕ in Finset.Icc 64 127, Int.floor (Real.logb 2 (k : ℝ))) = 384 := by
  have h1 : ∀ k : ℕ, k ∈ Finset.Icc 64 127 → Int.floor (Real.logb 2 (k : ℝ)) = 6 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h2 : 64 ≤ k := hk.1
    have h3 : k ≤ 127 := hk.2
    have h4 : k < 2 ^ (6 + 1) := by omega
    have h5 : 2 ^ 6 ≤ k := by omega
    have h6 : Int.floor (Real.logb 2 (k : ℝ)) = 6 := round12_floor_logb_interval_7cc0ce84 6 k h5 h4
    exact h6
  have h2 : (∑ k : ℕ in Finset.Icc 64 127, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 64 127, 6) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  <;> norm_num


lemma round10_sum_128_255_7cc0efa4 : (∑ k : ℕ in Finset.Icc 128 255, Int.floor (Real.logb 2 (k : ℝ))) = 896 := by
  have h1 : ∀ k : ℕ, k ∈ Finset.Icc 128 255 → Int.floor (Real.logb 2 (k : ℝ)) = 7 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h2 : 128 ≤ k := hk.1
    have h3 : k ≤ 255 := hk.2
    have h4 : k < 2 ^ (7 + 1) := by omega
    have h5 : 2 ^ 7 ≤ k := by omega
    have h6 : Int.floor (Real.logb 2 (k : ℝ)) = 7 := round12_floor_logb_interval_7cc0ce84 7 k h5 h4
    exact h6
  have h2 : (∑ k : ℕ in Finset.Icc 128 255, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 128 255, 7) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  <;> norm_num


lemma round7_h_sum_1_255 : (∑ k : ℕ in Finset.Icc 1 255, Int.floor (Real.logb 2 (k : ℝ))) = 1538 := by
  have h1 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 1 255 1 (by norm_num) (by norm_num)
  have h2 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 2 255 3 (by norm_num) (by norm_num)
  have h3 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 4 255 7 (by norm_num) (by norm_num)
  have h4 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 8 255 15 (by norm_num) (by norm_num)
  have h5 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 16 255 31 (by norm_num) (by norm_num)
  have h6 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 32 255 63 (by norm_num) (by norm_num)
  have h7 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 64 255 127 (by norm_num) (by norm_num)
  norm_num [h1, h2, h3, h4, h5, h6, h7, round10_sum_1_1_7cc0c538, round10_sum_2_3_7cc0d4d8, round10_sum_4_7_7cc0d938, round10_sum_8_15_7cc0dd70, round10_sum_16_31_7cc0e1b2, round10_sum_32_63_7cc0e63a, round10_sum_64_127_7cc0eb08, round10_sum_128_255_7cc0efa4] <;> linarith


lemma round7_h_sum_1_255_b5cb3520 : (∑ k : ℕ in Finset.Icc 1 255, Int.floor (Real.logb 2 (k : ℝ))) = 1538 := by
  have h1 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 1 255 1 (by norm_num) (by norm_num)
  have h2 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 2 255 3 (by norm_num) (by norm_num)
  have h3 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 4 255 7 (by norm_num) (by norm_num)
  have h4 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 8 255 15 (by norm_num) (by norm_num)
  have h5 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 16 255 31 (by norm_num) (by norm_num)
  have h6 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 32 255 63 (by norm_num) (by norm_num)
  have h7 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 64 255 127 (by norm_num) (by norm_num)
  norm_num [h1, h2, h3, h4, h5, h6, h7, round10_sum_1_1_7cc0c538, round10_sum_2_3_7cc0d4d8, round10_sum_4_7_7cc0d938, round10_sum_8_15_7cc0dd70, round10_sum_16_31_7cc0e1b2, round10_sum_32_63_7cc0e63a, round10_sum_64_127_7cc0eb08, round10_sum_128_255_7cc0efa4] <;> linarith


lemma round8_h_logb_256_311_b5cb394e (k : ℕ) (hk1 : 256 ≤ k) (hk2 : k ≤ 311) :
    Int.floor (Real.logb 2 (k : ℝ)) = 8 := by
  have h1 : (k : ℝ) > 0 := by
    have h_k_ge_256 : (k : ℝ) ≥ 256 := by exact_mod_cast hk1
    linarith
  have h2 : (2 : ℝ) > 1 := by norm_num
  have h3 : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have h4 : (256 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have h5 : (k : ℝ) < 512 := by
    have h_k_le_311 : (k : ℝ) ≤ 311 := by exact_mod_cast hk2
    linarith
  have h6 : Real.log 256 ≤ Real.log (k : ℝ) := by
    apply Real.log_le_log
    · linarith
    · linarith
  have h7 : Real.log (k : ℝ) < Real.log 512 := by
    apply Real.log_lt_log
    · linarith
    · linarith
  have h8 : Real.logb 2 256 = 8 := by
    have h81 : Real.log 256 = 8 * Real.log 2 := by
      have h82 : Real.log 256 = Real.log (2 ^ 8) := by norm_num
      have h83 : Real.log (2 ^ 8) = 8 * Real.log 2 := by
        rw [Real.log_pow] <;> norm_num
      rw [h82, h83]
    have h84 : Real.logb 2 256 = Real.log 256 / Real.log 2 := by
      rw [Real.logb]
    rw [h84, h81]
    field_simp [h3.ne']
    <;> ring
  have h9 : Real.logb 2 512 = 9 := by
    have h91 : Real.log 512 = 9 * Real.log 2 := by
      have h92 : Real.log 512 = Real.log (2 ^ 9) := by norm_num
      have h93 : Real.log (2 ^ 9) = 9 * Real.log 2 := by
        rw [Real.log_pow] <;> norm_num
      rw [h92, h93]
    have h94 : Real.logb 2 512 = Real.log 512 / Real.log 2 := by
      rw [Real.logb]
    rw [h94, h91]
    field_simp [h3.ne']
    <;> ring
  have h10 : 8 ≤ Real.logb 2 (k : ℝ) := by
    have h8_def : Real.logb 2 256 = Real.log 256 / Real.log 2 := by rw [Real.logb]
    have h10_ineq : Real.log 256 / Real.log 2 ≤ Real.log (k : ℝ) / Real.log 2 := by
      apply (div_le_div_right h3).mpr
      exact h6
    have h101 : Real.logb 2 256 ≤ Real.logb 2 (k : ℝ) := by
      rw [h8_def]
      exact h10_ineq
    have h102 : Real.logb 2 256 = 8 := h8
    linarith
  have h11 : Real.logb 2 (k : ℝ) < 9 := by
    have h9_def : Real.logb 2 512 = Real.log 512 / Real.log 2 := by rw [Real.logb]
    have h11_ineq : Real.log (k : ℝ) / Real.log 2 < Real.log 512 / Real.log 2 := by
      apply (div_lt_div_right h3).mpr
      exact h7
    have h111 : Real.logb 2 (k : ℝ) < Real.logb 2 512 := by
      rw [h9_def]
      exact h11_ineq
    have h112 : Real.logb 2 512 = 9 := h9
    linarith
  have h12 : (8 : ℝ) ≤ Real.logb 2 (k : ℝ) ∧ Real.logb 2 (k : ℝ) < (8 : ℝ) + 1 := ⟨by linarith, by linarith⟩
  have h13 : Int.floor (Real.logb 2 (k : ℝ)) = 8 := by
    rw [Int.floor_eq_iff]
    norm_num at h12 ⊢ <;> constructor <;> linarith
  exact h13


lemma round8_sum_Icc_1_311 : (∑ k : ℕ in Finset.Icc 1 311, Int.floor (Real.logb 2 (k : ℝ))) = 1986 := by
  have h1 : (∑ k : ℕ in Finset.Icc 1 311, Int.floor (Real.logb 2 (k : ℝ))) =
            (∑ k : ℕ in Finset.Icc 1 255, Int.floor (Real.logb 2 (k : ℝ))) +
            (∑ k : ℕ in Finset.Icc 256 311, Int.floor (Real.logb 2 (k : ℝ))) := by
    have h2 : Finset.Icc 1 311 = Finset.Icc 1 255 ∪ Finset.Icc 256 311 := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union]
      constructor
      · intro h
        have h3 : 1 ≤ x := h.1
        have h4 : x ≤ 311 := h.2
        by_cases h5 : x ≤ 255
        · left
          exact ⟨h3, h5⟩
        · right
          have h6 : 256 ≤ x := by linarith
          exact ⟨h6, h4⟩
      · intro h
        cases h with
        | inl h =>
          have h3 : 1 ≤ x := h.1
          have h4 : x ≤ 255 := h.2
          have h5 : x ≤ 311 := by linarith
          exact ⟨h3, h5⟩
        | inr h =>
          have h3 : 256 ≤ x := h.1
          have h4 : x ≤ 311 := h.2
          have h5 : 1 ≤ x := by linarith
          exact ⟨h5, h4⟩
    have h3 : Disjoint (Finset.Icc 1 255) (Finset.Icc 256 311) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1 hx2
      linarith
    rw [h2]
    rw [Finset.sum_union h3]
  rw [h1]
  have h2 : (∑ k : ℕ in Finset.Icc 256 311, Int.floor (Real.logb 2 (k : ℝ))) = ∑ k : ℕ in Finset.Icc 256 311, (8 : ℤ) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h3 : 256 ≤ k := hk.1
    have h4 : k ≤ 311 := hk.2
    exact round8_h_logb_256_311_b5cb394e k h3 h4
  have h3 : (∑ k : ℕ in Finset.Icc 256 311, (8 : ℤ)) = 448 := by
    simp [Finset.sum_const, nsmul_eq_mul]
    <;> norm_num
  have h4 : (∑ k : ℕ in Finset.Icc 1 255, Int.floor (Real.logb 2 (k : ℝ))) = 1538 := round7_h_sum_1_255_b5cb3520
  rw [h2, h3, h4]
  <;> norm_num


lemma round7_h_sum_1_255_a13fc706 : (∑ k : ℕ in Finset.Icc 1 255, Int.floor (Real.logb 2 (k : ℝ))) = 1538 := by
  have h1 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 1 255 1 (by norm_num) (by norm_num)
  have h2 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 2 255 3 (by norm_num) (by norm_num)
  have h3 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 4 255 7 (by norm_num) (by norm_num)
  have h4 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 8 255 15 (by norm_num) (by norm_num)
  have h5 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 16 255 31 (by norm_num) (by norm_num)
  have h6 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 32 255 63 (by norm_num) (by norm_num)
  have h7 := round9_sum_split_7cc0bfa2 (fun k => Int.floor (Real.logb 2 (k : ℝ))) 64 255 127 (by norm_num) (by norm_num)
  norm_num [h1, h2, h3, h4, h5, h6, h7, round10_sum_1_1_7cc0c538, round10_sum_2_3_7cc0d4d8, round10_sum_4_7_7cc0d938, round10_sum_8_15_7cc0dd70, round10_sum_16_31_7cc0e1b2, round10_sum_32_63_7cc0e63a, round10_sum_64_127_7cc0eb08, round10_sum_128_255_7cc0efa4] <;> linarith


lemma round8_h_logb_2_256_eq_8_a13fcb48 : Real.logb 2 256 = 8 := by
  have h1 : Real.logb 2 256 = Real.log 256 / Real.log 2 := by
    rw [Real.logb]
  have h2 : Real.log 256 = 8 * Real.log 2 := by
    have h21 : (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
    have h22 : Real.log 256 = Real.log ((2 : ℝ) ^ 8) := by rw [h21]
    have h23 : Real.log ((2 : ℝ) ^ 8) = 8 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h22, h23]
  have h3 : Real.log 2 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h4 : Real.log 2 ≠ 0 := by linarith
  rw [h1, h2]
  field_simp [h4]
  <;> ring


lemma round8_h_logb_2_512_eq_9_a13fcfa8 : Real.logb 2 512 = 9 := by
  have h1 : Real.logb 2 512 = Real.log 512 / Real.log 2 := by
    rw [Real.logb]
  have h2 : Real.log 512 = 9 * Real.log 2 := by
    have h21 : (512 : ℝ) = (2 : ℝ) ^ 9 := by norm_num
    have h22 : Real.log 512 = Real.log ((2 : ℝ) ^ 9) := by rw [h21]
    have h23 : Real.log ((2 : ℝ) ^ 9) = 9 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h22, h23]
  have h3 : Real.log 2 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h4 : Real.log 2 ≠ 0 := by linarith
  rw [h1, h2]
  field_simp [h4]
  <;> ring


lemma round8_h_floor_logb_2_eq_8_for_256_to_313_a13fd408 (k : ℕ) (hk1 : 256 ≤ k) (hk2 : k ≤ 313) :
    Int.floor (Real.logb 2 (k : ℝ)) = 8 := by
  have hk1' : (256 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ (313 : ℝ) := by exact_mod_cast hk2
  have h_k_pos : 0 < (k : ℝ) := by linarith
  have h_logb256 : Real.logb 2 256 = 8 := round8_h_logb_2_256_eq_8_a13fcb48
  have h_logb512 : Real.logb 2 512 = 9 := round8_h_logb_2_512_eq_9_a13fcfa8
  have h5 : Real.logb 2 (k : ℝ) ≥ 8 := by
    have h6 : Real.logb 2 256 ≤ Real.logb 2 (k : ℝ) := by
      have h_base_gt_one : (1 : ℝ) < 2 := by norm_num
      have h_256_pos : (0 : ℝ) < 256 := by norm_num
      exact Real.logb_le_logb_of_le h_base_gt_one h_256_pos hk1'
    linarith [h_logb256]
  have h6 : Real.logb 2 (k : ℝ) < 9 := by
    have h7 : (k : ℝ) < 512 := by linarith
    have h8 : Real.logb 2 (k : ℝ) < Real.logb 2 512 := by
      apply Real.logb_lt_logb <;> norm_num <;> linarith
    linarith [h_logb512]
  have h9 : 8 ≤ Real.logb 2 (k : ℝ) := by linarith
  have h10 : Real.logb 2 (k : ℝ) < 9 := by linarith
  have h11 : Int.floor (Real.logb 2 (k : ℝ)) = 8 := by
    rw [Int.floor_eq_iff] <;> norm_num <;> constructor <;> linarith
  exact h11


lemma round11_sum_256_313_a13fd908 : (∑ k : ℕ in Finset.Icc 256 313, Int.floor (Real.logb 2 (k : ℝ))) = 464 := by
  have h : ∀ k : ℕ, k ∈ Finset.Icc 256 313 → Int.floor (Real.logb 2 (k : ℝ)) = 8 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : 256 ≤ k := hk.1
    have hk2 : k ≤ 313 := hk.2
    exact round8_h_floor_logb_2_eq_8_for_256_to_313_a13fd408 k hk1 hk2
  have h2 : (∑ k : ℕ in Finset.Icc 256 313, Int.floor (Real.logb 2 (k : ℝ))) = ∑ k : ℕ in Finset.Icc 256 313, 8 := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h k hk
  rw [h2]
  norm_num [Finset.sum_const, nsmul_eq_mul]
  <;> decide


lemma round8_sum_Icc_1_313 : (∑ k : ℕ in Finset.Icc 1 313, Int.floor (Real.logb 2 (k : ℝ))) = 2002 := by
  have h1 : (∑ k : ℕ in Finset.Icc 1 313, Int.floor (Real.logb 2 (k : ℝ))) =
    (∑ k : ℕ in Finset.Icc 1 255, Int.floor (Real.logb 2 (k : ℝ))) + (∑ k : ℕ in Finset.Icc 256 313, Int.floor (Real.logb 2 (k : ℝ))) := by
    have h2 : 1 ≤ 255 := by decide
    have h3 : 255 < 313 := by decide
    have h4 : Finset.Icc 1 313 = Finset.Icc 1 255 ∪ Finset.Icc 256 313 := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union]
      constructor
      · intro hx
        have h5 : 1 ≤ x ∧ x ≤ 313 := hx
        by_cases h6 : x ≤ 255
        · have h7 : 1 ≤ x ∧ x ≤ 255 := ⟨h5.1, h6⟩
          exact Or.inl h7
        · have h7 : 256 ≤ x := by linarith
          have h8 : 256 ≤ x ∧ x ≤ 313 := ⟨h7, h5.2⟩
          exact Or.inr h8
      · intro hx
        cases hx with
        | inl h =>
          have h5 : 1 ≤ x ∧ x ≤ 255 := h
          have h6 : 1 ≤ x ∧ x ≤ 313 := ⟨h5.1, by linarith⟩
          exact h6
        | inr h =>
          have h5 : 256 ≤ x ∧ x ≤ 313 := h
          have h6 : 1 ≤ x ∧ x ≤ 313 := ⟨by linarith, h5.2⟩
          exact h6
    have h5 : Disjoint (Finset.Icc 1 255) (Finset.Icc 256 313) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1 hx2
      linarith
    have h6 : (∑ k : ℕ in Finset.Icc 1 313, Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in (Finset.Icc 1 255 ∪ Finset.Icc 256 313), Int.floor (Real.logb 2 (k : ℝ))) := by rw [h4]
    have h7 : (∑ k : ℕ in (Finset.Icc 1 255 ∪ Finset.Icc 256 313), Int.floor (Real.logb 2 (k : ℝ))) = (∑ k : ℕ in Finset.Icc 1 255, Int.floor (Real.logb 2 (k : ℝ))) + (∑ k : ℕ in Finset.Icc 256 313, Int.floor (Real.logb 2 (k : ℝ))) := by
      rw [Finset.sum_union] <;> aesop
    rw [h6, h7]
  rw [h1]
  rw [round7_h_sum_1_255_a13fc706]
  rw [round11_sum_256_313_a13fd908]
  <;> norm_num


lemma round9_sum_of_nonneg_is_nonneg (a b : ℕ) (ha : 1 ≤ a) :
    0 ≤ ∑ k in Finset.Icc a b, Int.floor (Real.logb 2 (k : ℝ)) := by
  apply Finset.sum_nonneg
  intro k hk
  have h₃ : a ≤ k := by
    simp only [Finset.mem_Icc] at hk
    linarith
  have h₄ : 1 ≤ k := by linarith
  exact round6_h_logb_nonneg k h₄


lemma round9_sum_split (m₁ m₂ : ℕ) (h_le : m₁ ≤ m₂) :
    (∑ k in Finset.Icc 1 m₂, Int.floor (Real.logb 2 (k:ℝ))) =
    (∑ k in Finset.Icc 1 m₁, Int.floor (Real.logb 2 (k:ℝ))) +
    (∑ k in Finset.Icc (m₁ + 1) m₂, Int.floor (Real.logb 2 (k:ℝ))) := by
  induction m₂ generalizing m₁ with
  | zero =>
    have h₁ : m₁ = 0 := by omega
    rw [h₁]
    <;> simp
  | succ m₂ ih =>
    by_cases h₂ : m₁ ≤ m₂
    · have h₃ : ∑ k in Finset.Icc 1 (m₂ + 1), Int.floor (Real.logb 2 (k : ℝ)) = (∑ k in Finset.Icc 1 m₂, Int.floor (Real.logb 2 (k : ℝ))) + Int.floor (Real.logb 2 ((m₂ + 1 : ℕ) : ℝ)) := by
        have h₄ : 1 ≤ m₂ + 1 := by omega
        simp [Finset.sum_Icc_succ_top h₄]
      have h₄ : ∑ k in Finset.Icc (m₁ + 1) (m₂ + 1), Int.floor (Real.logb 2 (k : ℝ)) = (∑ k in Finset.Icc (m₁ + 1) m₂, Int.floor (Real.logb 2 (k : ℝ))) + Int.floor (Real.logb 2 ((m₂ + 1 : ℕ) : ℝ)) := by
        have h₅ : m₁ + 1 ≤ m₂ + 1 := by omega
        simp [Finset.sum_Icc_succ_top h₅]
      have ih' := ih m₁ h₂
      rw [h₃, h₄, ih']
      <;> ring
    · have h₃ : m₁ = m₂ + 1 := by omega
      rw [h₃]
      <;> simp
      <;> ring


lemma round9_sum_mono (m₁ m₂ : ℕ) (h_le : m₁ ≤ m₂) :
    (∑ k in Finset.Icc 1 m₁, Int.floor (Real.logb 2 (k : ℝ))) ≤ (∑ k in Finset.Icc 1 m₂, Int.floor (Real.logb 2 (k : ℝ))) := by
  have h_split : (∑ k in Finset.Icc 1 m₂, Int.floor (Real.logb 2 (k : ℝ))) =
      (∑ k in Finset.Icc 1 m₁, Int.floor (Real.logb 2 (k : ℝ))) +
      (∑ k in Finset.Icc (m₁ + 1) m₂, Int.floor (Real.logb 2 (k : ℝ))) := round9_sum_split m₁ m₂ h_le
  have h_nonneg : 0 ≤ ∑ k in Finset.Icc (m₁ + 1) m₂, Int.floor (Real.logb 2 (k : ℝ)) := by
    have h₁ : 1 ≤ m₁ + 1 := by omega
    exact round9_sum_of_nonneg_is_nonneg (m₁ + 1) m₂ h₁
  linarith [h_split]


lemma round9_h_sum_mono (m₁ m₂ : ℕ) (h_le : m₁ ≤ m₂) :
    (∑ k in Finset.Icc 1 m₁, Int.floor (Real.logb 2 (k : ℝ))) ≤ (∑ k in Finset.Icc 1 m₂, Int.floor (Real.logb 2 (k : ℝ))) := by
  exact round9_sum_mono m₁ m₂ h_le


lemma round13_sum_equiv (n : ℕ) :
    (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 (k : ℝ))) := by
  apply Finset.sum_congr rfl
  intro k _
  rfl


lemma round12_h_n_le_312 (n : ℕ) (h₀ : 0 < n) (h₁ : (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = 1994) : n ≤ 312 := by
  by_contra h_contra
  have h_n_ge_313 : n ≥ 313 := by omega
  have h₁' : (∑ k : ℕ in Finset.Icc 1 n, Int.floor (Real.logb 2 (k : ℝ))) = 1994 := by
    have h_sum_equiv : (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 (k : ℝ))) := round13_sum_equiv n
    linarith [h₁, h_sum_equiv]
  have h_sum_ge : (∑ k : ℕ in Finset.Icc 1 313, Int.floor (Real.logb 2 (k : ℝ))) ≤ (∑ k : ℕ in Finset.Icc 1 n, Int.floor (Real.logb 2 (k : ℝ))) := by
    apply round9_h_sum_mono 313 n h_n_ge_313
  have h_S313 : (∑ k : ℕ in Finset.Icc 1 313, Int.floor (Real.logb 2 (k : ℝ))) = 2002 := round8_sum_Icc_1_313
  linarith [h_sum_ge, h₁', h_S313]


lemma round12_h_n_ge_312 (n : ℕ) (h₀ : 0 < n) (h₁ : (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = 1994) : n ≥ 312 := by
  by_contra h_contra
  have h_n_le_311 : n ≤ 311 := by omega
  have h₁' : (∑ k : ℕ in Finset.Icc 1 n, Int.floor (Real.logb 2 (k : ℝ))) = 1994 := by
    have h_sum_equiv : (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 (k : ℝ))) := round13_sum_equiv n
    linarith [h₁, h_sum_equiv]
  have h_sum_le : (∑ k : ℕ in Finset.Icc 1 n, Int.floor (Real.logb 2 (k : ℝ))) ≤ (∑ k : ℕ in Finset.Icc 1 311, Int.floor (Real.logb 2 (k : ℝ))) := by
    apply round9_h_sum_mono n 311 h_n_le_311
  have h_S311 : (∑ k : ℕ in Finset.Icc 1 311, Int.floor (Real.logb 2 (k : ℝ))) = 1986 := round8_sum_Icc_1_311
  linarith [h_sum_le, h₁', h_S311]


theorem aime_1994_p4 (n : ℕ) (h₀ : 0 < n)
    (h₀ : (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = 1994) : n = 312 := by
  have h_sum_eq : (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = 1994 := h₀
  have h_pos : 0 < n := by
    by_contra h
    have h₂ : n = 0 := by omega
    rw [h₂] at h_sum_eq
    norm_num at h_sum_eq <;> linarith
  have h_le : n ≤ 312 := round12_h_n_le_312 n h_pos h_sum_eq
  have h_ge : n ≥ 312 := round12_h_n_ge_312 n h_pos h_sum_eq
  omega
