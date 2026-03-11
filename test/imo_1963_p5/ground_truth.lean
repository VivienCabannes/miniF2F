import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1963_p5 :
  Real.cos (π / 7) - Real.cos (2 * π / 7) + Real.cos (3 * π / 7) = 1 / 2 := by
  have h1 : 2 * Real.sin (Real.pi / 7) * (Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7)) = Real.sin (Real.pi / 7) := by
    have h1₁ : 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) = Real.sin (2 * Real.pi / 7) := by
      have h1₁₁ : Real.sin (2 * Real.pi / 7) = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) := by
        have h1₁₂ : Real.sin (2 * Real.pi / 7) = Real.sin (2 * (Real.pi / 7)) := by ring
        rw [h1₁₂]
        have h1₁₃ : Real.sin (2 * (Real.pi / 7)) = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) := by
          rw [Real.sin_two_mul]
          <;> ring
        rw [h1₁₃]
        <;> ring
      linarith
    have h1₂ : 2 * Real.sin (Real.pi / 7) * Real.cos (2 * Real.pi / 7) = Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7) := by
      have h1₂₁ : 2 * Real.sin (Real.pi / 7) * Real.cos (2 * Real.pi / 7) = Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7) := by
        have h1₂₂ : Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7) = 2 * Real.sin (Real.pi / 7) * Real.cos (2 * Real.pi / 7) := by
          have h1₂₃ : Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7) = 2 * Real.sin ((3 * Real.pi / 7 - Real.pi / 7) / 2) * Real.cos ((3 * Real.pi / 7 + Real.pi / 7) / 2) := by
            have h1₂₄ : Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7) = 2 * Real.sin ((3 * Real.pi / 7 - Real.pi / 7) / 2) * Real.cos ((3 * Real.pi / 7 + Real.pi / 7) / 2) := by
              rw [← Real.sin_sub_sin]
              <;> ring_nf
              <;> field_simp
              <;> ring_nf
            rw [h1₂₄]
          rw [h1₂₃]
          have h1₂₅ : (3 * Real.pi / 7 - Real.pi / 7) / 2 = Real.pi / 7 := by ring
          have h1₂₆ : (3 * Real.pi / 7 + Real.pi / 7) / 2 = 2 * Real.pi / 7 := by ring
          rw [h1₂₅, h1₂₆]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
        linarith
      linarith
    have h1₃ : 2 * Real.sin (Real.pi / 7) * Real.cos (3 * Real.pi / 7) = Real.sin (4 * Real.pi / 7) - Real.sin (2 * Real.pi / 7) := by
      have h1₃₁ : 2 * Real.sin (Real.pi / 7) * Real.cos (3 * Real.pi / 7) = Real.sin (4 * Real.pi / 7) - Real.sin (2 * Real.pi / 7) := by
        have h1₃₂ : Real.sin (4 * Real.pi / 7) - Real.sin (2 * Real.pi / 7) = 2 * Real.sin (Real.pi / 7) * Real.cos (3 * Real.pi / 7) := by
          have h1₃₃ : Real.sin (4 * Real.pi / 7) - Real.sin (2 * Real.pi / 7) = 2 * Real.sin ((4 * Real.pi / 7 - 2 * Real.pi / 7) / 2) * Real.cos ((4 * Real.pi / 7 + 2 * Real.pi / 7) / 2) := by
            have h1₃₄ : Real.sin (4 * Real.pi / 7) - Real.sin (2 * Real.pi / 7) = 2 * Real.sin ((4 * Real.pi / 7 - 2 * Real.pi / 7) / 2) * Real.cos ((4 * Real.pi / 7 + 2 * Real.pi / 7) / 2) := by
              rw [← Real.sin_sub_sin]
              <;> ring_nf
              <;> field_simp
              <;> ring_nf
            rw [h1₃₄]
          rw [h1₃₃]
          have h1₃₅ : (4 * Real.pi / 7 - 2 * Real.pi / 7) / 2 = Real.pi / 7 := by ring
          have h1₃₆ : (4 * Real.pi / 7 + 2 * Real.pi / 7) / 2 = 3 * Real.pi / 7 := by ring
          rw [h1₃₅, h1₃₆]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
        linarith
      linarith
    have h1₄ : Real.sin (4 * Real.pi / 7) = Real.sin (3 * Real.pi / 7) := by
      have h1₄₁ : Real.sin (4 * Real.pi / 7) = Real.sin (Real.pi - 3 * Real.pi / 7) := by
        have h1₄₂ : 4 * Real.pi / 7 = Real.pi - 3 * Real.pi / 7 := by ring
        rw [h1₄₂]
        <;> simp [Real.sin_pi_sub]
      rw [h1₄₁]
      have h1₄₃ : Real.sin (Real.pi - 3 * Real.pi / 7) = Real.sin (3 * Real.pi / 7) := by
        simp [Real.sin_pi_sub]
      rw [h1₄₃]
    calc
      2 * Real.sin (Real.pi / 7) * (Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7)) = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) - 2 * Real.sin (Real.pi / 7) * Real.cos (2 * Real.pi / 7) + 2 * Real.sin (Real.pi / 7) * Real.cos (3 * Real.pi / 7) := by
        ring
      _ = Real.sin (2 * Real.pi / 7) - (Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7)) + (Real.sin (4 * Real.pi / 7) - Real.sin (2 * Real.pi / 7)) := by
        rw [h1₁, h1₂, h1₃]
        <;> ring
      _ = Real.sin (2 * Real.pi / 7) - Real.sin (3 * Real.pi / 7) + Real.sin (Real.pi / 7) + (Real.sin (4 * Real.pi / 7) - Real.sin (2 * Real.pi / 7)) := by
        ring
      _ = Real.sin (Real.pi / 7) := by
        rw [h1₄]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
        <;> linarith [Real.sin_le_one (3 * Real.pi / 7), Real.sin_le_one (Real.pi / 7)]
  
  have h2 : Real.sin (Real.pi / 7) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos, Real.pi_gt_three]
    · linarith [Real.pi_pos, Real.pi_gt_three]
  
  have h3 : Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = 1 / 2 := by
    have h3₁ : 2 * Real.sin (Real.pi / 7) > 0 := by linarith
    have h3₂ : Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = 1 / 2 := by
      apply mul_left_cancel₀ (show (2 * Real.sin (Real.pi / 7) : ℝ) ≠ 0 by linarith)
      nlinarith [Real.sin_le_one (Real.pi / 7), Real.sin_le_one (2 * Real.pi / 7), Real.sin_le_one (3 * Real.pi / 7),
        Real.sin_le_one (4 * Real.pi / 7), Real.sin_le_one (Real.pi / 7)]
    exact h3₂
  
  apply h3