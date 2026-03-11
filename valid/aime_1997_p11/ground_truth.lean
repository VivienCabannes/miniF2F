import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1997_p11 (x : ℝ)
    (h₀ :
      x =
        (∑ n ∈ Finset.Icc (1 : ℕ) 44, Real.cos (n * π / 180)) /
          ∑ n ∈ Finset.Icc (1 : ℕ) 44, Real.sin (n * π / 180)) :
    Int.floor (100 * x) = 241 := by
  have h₁ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) > 0 := by
    have h₁₀ : ∀ (n : ℕ), n ∈ Finset.Icc (1 : ℕ) 44 → Real.sin (n * Real.pi / 180) > 0 := by
      intro n hn
      have h₁₁ : 1 ≤ n ∧ n ≤ 44 := Finset.mem_Icc.mp hn
      have h₁₂ : 1 ≤ (n : ℝ) := by exact_mod_cast h₁₁.1
      have h₁₃ : (n : ℝ) ≤ 44 := by exact_mod_cast h₁₁.2
      have h₁₄ : 0 < (n : ℝ) * Real.pi / 180 := by
        have h₁₅ : 0 < Real.pi := Real.pi_pos
        have h₁₆ : 0 < (n : ℝ) := by linarith
        positivity
      have h₁₅ : (n : ℝ) * Real.pi / 180 < Real.pi := by
        have h₁₆ : (n : ℝ) ≤ 44 := by exact_mod_cast h₁₁.2
        have h₁₇ : 0 < Real.pi := Real.pi_pos
        nlinarith [Real.pi_gt_three]
      have h₁₆ : Real.sin ((n : ℝ) * Real.pi / 180) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · exact h₁₄
        · exact h₁₅
      exact_mod_cast h₁₆
    have h₁₇ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) > 0 := by
      apply Finset.sum_pos
      · intro n hn
        exact h₁₀ n hn
      · exact ⟨1, by
          norm_num [Finset.mem_Icc]
          <;>
          (try norm_num) <;>
          (try linarith [Real.pi_gt_three])⟩
    exact h₁₇
  
  have h₂ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180) = (1 + Real.sqrt 2) * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := by
    have h₂₁ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180) - ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) = Real.sqrt 2 * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := by
      have h₂₂ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180) - ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) = ∑ n in Finset.Icc (1 : ℕ) 44, (Real.cos (n * Real.pi / 180) - Real.sin (n * Real.pi / 180)) := by
        rw [← Finset.sum_sub_distrib]
      rw [h₂₂]
      have h₂₃ : ∑ n in Finset.Icc (1 : ℕ) 44, (Real.cos (n * Real.pi / 180) - Real.sin (n * Real.pi / 180)) = Real.sqrt 2 * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := by
        have h₂₄ : ∑ n in Finset.Icc (1 : ℕ) 44, (Real.cos (n * Real.pi / 180) - Real.sin (n * Real.pi / 180)) = ∑ n in Finset.Icc (1 : ℕ) 44, Real.sqrt 2 * Real.sin ((45 - n : ℕ) * Real.pi / 180) := by
          apply Finset.sum_congr rfl
          intro n hn
          have h₂₅ : n ∈ Finset.Icc (1 : ℕ) 44 := hn
          have h₂₆ : 1 ≤ n ∧ n ≤ 44 := Finset.mem_Icc.mp h₂₅
          have h₂₇ : Real.cos (n * Real.pi / 180) - Real.sin (n * Real.pi / 180) = Real.sqrt 2 * Real.sin ((45 - n : ℕ) * Real.pi / 180) := by
            have h₂₈ : (n : ℕ) ≤ 44 := by linarith
            have h₂₉ : (n : ℕ) ≥ 1 := by linarith
            have h₃₀ : Real.cos (n * Real.pi / 180) - Real.sin (n * Real.pi / 180) = Real.sqrt 2 * Real.sin ((45 - n : ℕ) * Real.pi / 180) := by
              have h₃₁ : Real.sin ((45 - n : ℕ) * Real.pi / 180) = Real.sin ((45 - n : ℕ) * Real.pi / 180) := rfl
              rw [h₃₁]
              have h₃₂ : Real.cos (n * Real.pi / 180) - Real.sin (n * Real.pi / 180) = Real.sqrt 2 * Real.sin ((45 - n : ℕ) * Real.pi / 180) := by
                have h₃₃ : Real.sin ((45 - n : ℕ) * Real.pi / 180) = Real.sin (Real.pi / 4 - (n * Real.pi / 180)) := by
                  have h₃₄ : ((45 - n : ℕ) : ℝ) * Real.pi / 180 = Real.pi / 4 - (n * Real.pi / 180) := by
                    have h₃₅ : n ≤ 44 := by linarith
                    interval_cases n <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_sub, Nat.cast_mul] <;>
                      (try ring_nf) <;> (try field_simp) <;> (try ring_nf) <;> (try norm_num) <;> (try linarith [Real.pi_pos])
                    <;> (try ring_nf) <;> (try field_simp) <;> (try ring_nf) <;> (try norm_num) <;> (try linarith [Real.pi_pos])
                  rw [h₃₄]
                  <;> ring_nf
                rw [h₃₃]
                have h₃₄ : Real.sin (Real.pi / 4 - (n * Real.pi / 180)) = Real.sin (Real.pi / 4) * Real.cos (n * Real.pi / 180) - Real.cos (Real.pi / 4) * Real.sin (n * Real.pi / 180) := by
                  rw [Real.sin_sub]
                rw [h₃₄]
                have h₃₅ : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by norm_num
                have h₃₆ : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by norm_num
                rw [h₃₅, h₃₆]
                ring_nf
                <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num <;>
                  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
              rw [h₃₂]
            exact h₃₀
          rw [h₂₇]
        rw [h₂₄]
        have h₂₅ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.sqrt 2 * Real.sin ((45 - n : ℕ) * Real.pi / 180) = Real.sqrt 2 * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin ((45 - n : ℕ) * Real.pi / 180) := by
          rw [Finset.mul_sum]
        rw [h₂₅]
        have h₂₆ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin ((45 - n : ℕ) * Real.pi / 180) = ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := by
          have h₂₇ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin ((45 - n : ℕ) * Real.pi / 180) = ∑ k in Finset.Icc (1 : ℕ) 44, Real.sin (k * Real.pi / 180) := by
            apply Finset.sum_bij' (fun (n : ℕ) _ ↦ (45 - n : ℕ)) (fun (n : ℕ) _ ↦ (45 - n : ℕ))
            <;> simp_all [Finset.mem_Icc, Nat.le_of_lt_succ, Nat.succ_le_iff]
            <;>
              (try omega) <;>
              (try ring_nf) <;>
              (try simp_all [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]) <;>
              (try field_simp) <;>
              (try ring_nf) <;>
              (try norm_num) <;>
              (try linarith) <;>
              (try omega)
            <;>
              (try {
                rcases n with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
                  simp_all [Finset.mem_Icc, Nat.le_of_lt_succ, Nat.succ_le_iff] <;>
                  (try omega) <;>
                  (try ring_nf) <;>
                  (try simp_all [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]) <;>
                  (try field_simp) <;>
                  (try ring_nf) <;>
                  (try norm_num) <;>
                  (try linarith) <;>
                  (try omega)
              })
          rw [h₂₇]
        rw [h₂₆]
      rw [h₂₃]
      <;> ring_nf
      <;> linarith
    have h₂₂ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180) = (1 + Real.sqrt 2) * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := by
      have h₂₃ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180) - ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) = Real.sqrt 2 * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := h₂₁
      have h₂₄ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180) = (1 + Real.sqrt 2) * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := by
        linarith
      exact h₂₄
    exact h₂₂
  
  have h₃ : x = 1 + Real.sqrt 2 := by
    rw [h₀]
    have h₃₁ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) > 0 := h₁
    have h₃₂ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180) = (1 + Real.sqrt 2) * ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) := h₂
    have h₃₃ : (∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180)) / ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) = 1 + Real.sqrt 2 := by
      rw [h₃₂]
      have h₃₄ : ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180) ≠ 0 := by linarith
      field_simp [h₃₄]
      <;> ring_nf
      <;> field_simp [h₃₄]
      <;> linarith
    rw [h₃₃]
    <;> ring_nf
    <;> field_simp
    <;> linarith
  
  have h₄ : 100 * x = 100 + 100 * Real.sqrt 2 := by
    rw [h₃]
    <;> ring
    <;> field_simp
    <;> ring
    <;> linarith [Real.sqrt_nonneg 2]
  
  have h₅ : (241 : ℝ) ≤ 100 * x := by
    rw [h₄]
    have h₅₁ : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg _
    have h₅₂ : (141 : ℝ) ≤ 100 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num),
        Real.sqrt_nonneg 2, Real.pi_gt_three]
    linarith
  
  have h₆ : (100 : ℝ) * x < 242 := by
    rw [h₄]
    have h₆₁ : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg _
    have h₆₂ : (100 : ℝ) * Real.sqrt 2 < 142 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith
  
  have h₇ : Int.floor (100 * x) = 241 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h₅ h₆ ⊢ <;>
    (try linarith) <;>
    (try
      {
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      })
    <;>
    (try
      {
        norm_num at h₅ h₆ ⊢
        <;>
        (try linarith)
        <;>
        (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
      })
    <;>
    (try
      {
        norm_num [h₄] at h₅ h₆ ⊢
        <;>
        (try linarith)
        <;>
        (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
      })
    <;>
    (try
      {
        norm_num [h₄] at h₅ h₆ ⊢
        <;>
        (try linarith)
        <;>
        (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
      })
    <;>
    (try
      {
        norm_num [h₄] at h₅ h₆ ⊢
        <;>
        (try linarith)
        <;>
        (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
      })
    <;>
    (try
      {
        norm_num [h₄] at h₅ h₆ ⊢
        <;>
        (try linarith)
        <;>
        (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
      })
  
  rw [h₇]
  <;> norm_num
  <;>
  (try
    {
      norm_num at h₅ h₆ ⊢
      <;>
      (try linarith)
      <;>
      (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
    })
  <;>
  (try
    {
      norm_num [h₄] at h₅ h₆ ⊢
      <;>
      (try linarith)
      <;>
      (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
    })
  <;>
  (try
    {
      norm_num [h₄] at h₅ h₆ ⊢
      <;>
      (try linarith)
      <;>
      (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
    })
  <;>
  (try
    {
      norm_num [h₄] at h₅ h₆ ⊢
      <;>
      (try linarith)
      <;>
      (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
    })
  <;>
  (try
    {
      norm_num [h₄] at h₅ h₆ ⊢
      <;>
      (try linarith)
      <;>
      (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
    })
  <;>
  (try
    {
      norm_num [h₄] at h₅ h₆ ⊢
      <;>
      (try linarith)
      <;>
      (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
    })