import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p3
  (x : ℝ)
  (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) :
  x = 3 / 4 := by
  have h₁ : 3 + x ≠ 0 := by
    by_contra h
    have h₂ : 3 + x = 0 := by linarith
    have h₃ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 8 / 3 := by
      have h₄ : (3 + x : ℝ) = 0 := by simpa using h₂
      have h₅ : (2 : ℝ) + 2 / (3 + x) = 2 := by
        rw [h₄]
        norm_num
      have h₆ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = 3 / 2 := by
        rw [h₅]
        <;> norm_num
      have h₇ : (2 : ℝ) + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 8 / 3 := by
        rw [h₆]
        <;> norm_num
      linarith
    linarith
  
  have h₂ : 8 + 2 * x ≠ 0 := by
    by_contra h
    have h₂ : (8 + 2 * x : ℝ) = 0 := by linarith
    have h₃ : x = -4 := by linarith
    have h₄ : (2 : ℝ) + 2 / (3 + x) = 0 := by
      rw [h₃]
      <;> norm_num
    have h₅ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = 1 := by
      have h₅₁ : (2 : ℝ) + 2 / (3 + x) = 0 := by
        exact h₄
      have h₅₂ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = 1 := by
        rw [h₅₁]
        <;> norm_num
      exact h₅₂
    have h₆ : (2 : ℝ) + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 3 := by
      rw [h₅]
      <;> norm_num
    linarith
  
  have h₃ : 11 + 3 * x ≠ 0 := by
    by_contra h
    have h₃ : (11 + 3 * x : ℝ) = 0 := by linarith
    have h₄ : x = -11 / 3 := by linarith
    have h₅ : (2 : ℝ) + 2 / (3 + x) = -1 := by
      rw [h₄]
      <;> norm_num
    have h₆ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = 0 := by
      have h₆₁ : (2 : ℝ) + 2 / (3 + x) = -1 := by
        exact h₅
      have h₆₂ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = 0 := by
        rw [h₆₁]
        <;> norm_num
      exact h₆₂
    have h₇ : (2 : ℝ) + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 2 := by
      rw [h₆]
      <;> norm_num
    linarith
  
  have h₄ : (30 + 8 * x : ℝ) / (11 + 3 * x) = 144 / 53 := by
    have h₄₁ : (2 : ℝ) + 1 / (1 + 1 / (2 + 2 / (3 + x))) = (30 + 8 * x : ℝ) / (11 + 3 * x) := by
      have h₄₂ : (2 : ℝ) + 2 / (3 + x) = (8 + 2 * x : ℝ) / (3 + x) := by
        field_simp [h₁]
        <;> ring_nf
        <;> field_simp [h₁]
        <;> ring_nf
        <;> nlinarith
      have h₄₃ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = (11 + 3 * x : ℝ) / (8 + 2 * x) := by
        have h₄₄ : (2 : ℝ) + 2 / (3 + x) = (8 + 2 * x : ℝ) / (3 + x) := by
          exact h₄₂
        have h₄₅ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = (11 + 3 * x : ℝ) / (8 + 2 * x) := by
          have h₄₆ : (2 : ℝ) + 2 / (3 + x) = (8 + 2 * x : ℝ) / (3 + x) := by
            exact h₄₂
          have h₄₇ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = (1 : ℝ) + 1 / ((8 + 2 * x : ℝ) / (3 + x)) := by
            rw [h₄₆]
          rw [h₄₇]
          have h₄₈ : (1 : ℝ) + 1 / ((8 + 2 * x : ℝ) / (3 + x)) = (1 : ℝ) + (3 + x : ℝ) / (8 + 2 * x) := by
            field_simp [h₁, h₂]
            <;> ring_nf
            <;> field_simp [h₁, h₂]
            <;> nlinarith
          rw [h₄₈]
          have h₄₉ : (1 : ℝ) + (3 + x : ℝ) / (8 + 2 * x) = (11 + 3 * x : ℝ) / (8 + 2 * x) := by
            field_simp [h₂]
            <;> ring_nf
            <;> field_simp [h₂]
            <;> nlinarith
          rw [h₄₉]
          <;> field_simp [h₂]
          <;> ring_nf
          <;> field_simp [h₂]
          <;> nlinarith
        exact h₄₅
      have h₄₅ : (2 : ℝ) + 1 / (1 + 1 / (2 + 2 / (3 + x))) = (30 + 8 * x : ℝ) / (11 + 3 * x) := by
        have h₄₆ : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = (11 + 3 * x : ℝ) / (8 + 2 * x) := by
          exact h₄₃
        have h₄₇ : (2 : ℝ) + 1 / (1 + 1 / (2 + 2 / (3 + x))) = (2 : ℝ) + 1 / ((11 + 3 * x : ℝ) / (8 + 2 * x)) := by
          rw [h₄₆]
        rw [h₄₇]
        have h₄₈ : (2 : ℝ) + 1 / ((11 + 3 * x : ℝ) / (8 + 2 * x)) = (2 : ℝ) + (8 + 2 * x : ℝ) / (11 + 3 * x) := by
          field_simp [h₂, h₃]
          <;> ring_nf
          <;> field_simp [h₂, h₃]
          <;> nlinarith
        rw [h₄₈]
        have h₄₉ : (2 : ℝ) + (8 + 2 * x : ℝ) / (11 + 3 * x) = (30 + 8 * x : ℝ) / (11 + 3 * x) := by
          field_simp [h₃]
          <;> ring_nf
          <;> field_simp [h₃]
          <;> nlinarith
        rw [h₄₉]
        <;> field_simp [h₃]
        <;> ring_nf
        <;> field_simp [h₃]
        <;> nlinarith
      exact h₄₅
    have h₄₂ : (2 : ℝ) + 1 / (1 + 1 / (2 + 2 / (3 + x))) = (30 + 8 * x : ℝ) / (11 + 3 * x) := by
      exact h₄₁
    rw [h₄₂] at h₀
    have h₄₃ : (30 + 8 * x : ℝ) / (11 + 3 * x) = 144 / 53 := by
      linarith
    linarith
  
  have h₅ : x = 3 / 4 := by
    have h₅₁ : (30 + 8 * x : ℝ) / (11 + 3 * x) = 144 / 53 := by
      exact h₄
    have h₅₂ : (30 + 8 * x : ℝ) * 53 = (144 : ℝ) * (11 + 3 * x) := by
      have h₅₃ : (11 + 3 * x : ℝ) ≠ 0 := by simpa using h₃
      field_simp at h₅₁
      nlinarith
    have h₅₃ : x = 3 / 4 := by
      ring_nf at h₅₂
      nlinarith
    exact h₅₃
  
  rw [h₅]
  <;> norm_num
  <;> linarith