import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1974_p5 (a b c d s : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : s = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) :
  1 < s ∧ s < 2 := by
  have term1_pos : 0 < a / (a + b + d) := by
    have h₂ := h₀.1
    have h₃ := h₀.2.1
    have h₄ := h₀.2.2.1
    have h₅ := h₀.2.2.2
    have h₆ := h₁
    -- We need to show that the first term is positive.
    -- Since a, b, and d are all positive, the denominator (a + b + d) is positive.
    -- Therefore, the fraction a / (a + b + d) is positive.
    positivity
  
  have term1_less1 : a / (a + b + d) < 1 := by
    -- Show that the numerator is less than the denominator, which implies the fraction is less than 1.
    have h₂ : a < a + b + d := by linarith
    have h₃ : 0 < a + b + d := by linarith
    rw [div_lt_one] <;> linarith
  
  have term2_pos : 0 < b / (a + b + c) := by
    have h₂ : 0 < a + b + c := by linarith
    have h₃ : 0 < a + b + d := by linarith
    have h₄ : 0 < b + c + d := by linarith
    have h₅ : 0 < a + c + d := by linarith
    -- We need to show that the second term is positive.
    -- Since a, b, c, d are all positive, the numerator b is positive.
    -- The denominator a + b + c is also positive.
    -- Therefore, the second term b / (a + b + c) is positive.
    exact div_pos h₀.2.1 (by linarith)
  
  have term2_less1 : b / (a + b + c) < 1 := by
    -- We need to show that b / (a + b + c) < 1.
    have h₂ : 0 < a + b + c := by linarith [h₀.1, h₀.2.1, h₀.2.2.1]
    -- Since a, b, c are all positive, a + b + c is positive.
    have h₃ : 0 < a + b + d := by linarith [h₀.1, h₀.2.1, h₀.2.2.2]
    -- Since a, b, d are all positive, a + b + d is positive.
    have h₄ : 0 < b + c + d := by linarith [h₀.2.1, h₀.2.2.1, h₀.2.2.2]
    -- Since b, c, d are all positive, b + c + d is positive.
    have h₅ : 0 < a + c + d := by linarith [h₀.1, h₀.2.2.1, h₀.2.2.2]
    -- Since a, c, d are all positive, a + c + d is positive.
    -- Using the fact that each term is less than 1, we can conclude that b / (a + b + c) < 1.
    rw [← sub_pos] at term1_pos term1_less1 term2_pos ⊢
    field_simp at term1_pos term1_less1 term2_pos ⊢
    rw [← sub_pos] at term1_pos term1_less1 term2_pos ⊢
    field_simp at term1_pos term1_less1 term2_pos ⊢
    nlinarith [term1_pos, term1_less1, term2_pos]
  
  have term3_pos : 0 < c / (b + c + d) := by
    have h₂ := h₀.2.1
    have h₃ := h₀.2.2.1
    have h₄ := h₀.2.2.2
    have h₅ := term1_pos
    have h₆ := term1_less1
    have h₇ := term2_pos
    have h₈ := term2_less1
    have h₉ : 0 < a + b + c := by linarith
    have h₁₀ : 0 < a + b + d := by linarith
    have h₁₁ : 0 < a + c + d := by linarith
    have h₁₂ : 0 < b + c + d := by linarith
    have h₁₃ : 0 < a + b + c + d := by linarith
    field_simp at h₅ h₆ h₇ h₈ ⊢
    refine' lt_of_sub_pos _
    field_simp
    ring_nf
    nlinarith [mul_pos h₂ h₃, mul_pos h₂ h₄, mul_pos h₃ h₄,
      mul_pos (sub_pos.mpr h₅) (sub_pos.mpr h₆),
      mul_pos (sub_pos.mpr h₇) (sub_pos.mpr h₈)]
  
  have term3_less1 : c / (b + c + d) < 1 := by
    -- Use the fact that each term is less than 1 to prove the inequality for the third term.
    have h₂ : 0 < b + c + d := by linarith
    have h₃ : 0 < a + b + c := by linarith
    have h₄ : 0 < a + c + d := by linarith
    have h₅ : 0 < a + b + d := by linarith
    field_simp at term1_pos term1_less1 term2_pos term2_less1 term3_pos
    rw [div_lt_one] <;> linarith
  
  have term4_pos : 0 < d / (a + c + d) := by
    -- From the given conditions, we know that all variables are positive.
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < c := by linarith
    have h₅ : 0 < d := by linarith
    -- We need to show that the last term is positive.
    have h₆ : 0 < d / (a + c + d) := by positivity
    -- Since all terms are positive and less than 1, the sum S is less than 4.
    linarith
  
  have term4_less1 : d / (a + c + d) < 1 := by
    -- We already know from the given conditions that each term is less than 1.
    -- Specifically, term4_pos gives us that d / (a + c + d) is positive,
    -- and we need to show that it is less than 1.
    have h₂ : d / (a + c + d) < 1 := by
      -- Since d is positive and a + c + d is positive, we can use the division inequality.
      rw [div_lt_one] <;> nlinarith [h₀.1, h₀.2.1, h₀.2.2.1, h₀.2.2.2, term4_pos]
    -- The result h₂ directly gives us the desired inequality.
    exact h₂
  
  have s_pos : 0 < s := by
    -- Since each term in the sum is positive, the sum itself is positive.
    have h₂ : 0 < a / (a + b + d) := term1_pos
    have h₃ : 0 < b / (a + b + c) := term2_pos
    have h₄ : 0 < c / (b + c + d) := term3_pos
    have h₅ : 0 < d / (a + c + d) := term4_pos
    -- Using the fact that each term is positive, we can conclude that the sum s is positive.
    linarith [h₁, h₂, h₃, h₄, h₅]
  
  have lower_bound : 1 < s := by
    have h₂ : 0 < a + b + d := by linarith
    have h₃ : 0 < a + b + c := by linarith
    have h₄ : 0 < b + c + d := by linarith
    have h₅ : 0 < a + c + d := by linarith
    have h₆ : 0 < a + b + c + d := by linarith
    -- Combine all the fractions to show that the sum is greater than 1
    field_simp [h₁, h₂, h₃, h₄, h₅, h₆]
    refine' lt_of_sub_pos _
    field_simp
    ring_nf
    nlinarith [mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2.1, mul_pos h₀.2.2.1 h₀.2.2.2,
      mul_pos h₀.1 h₀.2.2.1, mul_pos h₀.1 h₀.2.2.2, mul_pos h₀.2.1 h₀.2.2.2]
  
  have upper_bound : s < 2 := by
    have h₂ : 0 < a + b + c + d := by linarith [h₀.1, h₀.2.1, h₀.2.2.1, h₀.2.2.2]
    have h₃ : 0 < a + b + d := by linarith [h₀.1, h₀.2.1, h₀.2.2.1]
    have h₄ : 0 < a + b + c := by linarith [h₀.1, h₀.2.1, h₀.2.2.2]
    have h₅ : 0 < b + c + d := by linarith [h₀.2.1, h₀.2.2.1, h₀.2.2.2]
    have h₆ : 0 < a + c + d := by linarith [h₀.1, h₀.2.2.1, h₀.2.2.2]
    field_simp [h₁] at term1_pos term1_less1 term2_pos term2_less1 term3_pos term3_less1 term4_pos term4_less1 s_pos lower_bound
    refine' lt_of_sub_pos _
    field_simp [h₁]
    ring_nf
    nlinarith [mul_pos h₀.1 h₀.2.1, mul_pos h₀.1 h₀.2.2.1, mul_pos h₀.1 h₀.2.2.2,
      mul_pos h₀.2.1 h₀.2.2.1, mul_pos h₀.2.1 h₀.2.2.2, mul_pos h₀.2.2.1 h₀.2.2.2]
  
  constructor
  -- Prove that 1 is less than s using the given lower_bound.
  exact lower_bound
  -- Prove that s is less than 2 using the given upper_bound.
  exact upper_bound