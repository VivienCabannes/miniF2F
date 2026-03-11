import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa
  (a b : ℝ) :
  abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h₁ : abs (a + b) ≤ abs a + abs b := by
    calc
      abs (a + b) ≤ abs a + abs b := by
        -- Use the triangle inequality for absolute values.
        exact abs_add a b
      _ = abs a + abs b := by rfl
  
  have h₂ : ∀ (x y : ℝ), 0 ≤ x → x ≤ y → x / (1 + x) ≤ y / (1 + y) := by
    intro x y hx hxy
    have h₃ : 0 ≤ x := hx
    have h₄ : x ≤ y := hxy
    have h₅ : 0 ≤ y := by linarith
    have h₆ : 0 ≤ 1 + x := by linarith
    have h₇ : 0 ≤ 1 + y := by linarith
    have h₈ : 0 < 1 + x := by linarith
    have h₉ : 0 < 1 + y := by linarith
    -- Use the division inequality to compare the fractions.
    have h₁₀ : x / (1 + x) ≤ y / (1 + y) := by
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Simplify the inequality to a form that can be handled by linear arithmetic.
      nlinarith [mul_nonneg h₃ (sub_nonneg.mpr h₄), mul_nonneg h₅ h₃,
        mul_nonneg h₅ (sub_nonneg.mpr h₄)]
    exact h₁₀
  
  have h₃ : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + (abs a + abs b)) := by
    have h₄ : 0 ≤ abs (a + b) := abs_nonneg (a + b)
    have h₅ : 0 ≤ abs a + abs b := by positivity
    have h₆ : abs (a + b) ≤ abs a + abs b := h₁
    have h₇ : 0 ≤ 1 + abs (a + b) := by positivity
    have h₈ : 0 ≤ 1 + (abs a + abs b) := by positivity
    have h₉ : 0 < 1 + abs (a + b) := by positivity
    have h₁₀ : 0 < 1 + (abs a + abs b) := by positivity
    -- Use the fact that the function x / (1 + x) is increasing for x ≥ 0.
    have h₁₁ : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + (abs a + abs b)) := by
      have h₁₂ : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + (abs a + abs b)) := by
        -- Apply the increasing property of the function.
        have h₁₃ : 0 ≤ abs (a + b) := by positivity
        have h₁₄ : abs (a + b) ≤ abs a + abs b := h₁
        have h₁₅ : 0 ≤ abs a + abs b := by positivity
        have h₁₆ : 0 < 1 + abs (a + b) := by positivity
        have h₁₇ : 0 < 1 + (abs a + abs b) := by positivity
        -- Use the previously proven lemma.
        have h₁₈ : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + (abs a + abs b)) := by
          apply h₂
          <;> try norm_num
          <;> linarith
        exact h₁₈
      exact h₁₂
    exact h₁₁
  
  have h₄ : (abs a + abs b) / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    have h₅ : 0 ≤ abs a := abs_nonneg a
    have h₆ : 0 ≤ abs b := abs_nonneg b
    have h₇ : 0 ≤ abs a + abs b := by positivity
    have h₈ : 0 < 1 + abs a := by positivity
    have h₉ : 0 < 1 + abs b := by positivity
    have h₁₀ : 0 < 1 + (abs a + abs b) := by positivity
    have h₁₁ : (abs a + abs b) / (1 + (abs a + abs b)) = abs a / (1 + (abs a + abs b)) + abs b / (1 + (abs a + abs b)) := by
      field_simp [h₈, h₉, h₁₀]
      <;> ring
      <;> field_simp [h₈, h₉, h₁₀]
      <;> ring
    rw [h₁₁]
    have h₁₂ : abs a / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) := by
      have h₁₃ : 0 ≤ abs a := abs_nonneg a
      have h₁₄ : 0 < 1 + abs a := by positivity
      have h₁₅ : 0 < 1 + (abs a + abs b) := by positivity
      have h₁₆ : 0 < 1 + abs a + abs b := by positivity
      -- Use the fact that 1 + abs a ≤ 1 + (abs a + abs b) to show the inequality
      have h₁₇ : 1 + abs a ≤ 1 + (abs a + abs b) := by
        nlinarith [h₆]
      -- Use the division inequality to prove the result
      have h₁₈ : abs a / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) := by
        apply div_le_div_of_le_left (by positivity) (by positivity)
        <;> nlinarith
      exact h₁₈
    have h₁₃ : abs b / (1 + (abs a + abs b)) ≤ abs b / (1 + abs b) := by
      have h₁₄ : 0 ≤ abs b := abs_nonneg b
      have h₁₅ : 0 < 1 + abs b := by positivity
      have h₁₆ : 0 < 1 + (abs a + abs b) := by positivity
      have h₁₇ : 0 < 1 + abs a + abs b := by positivity
      -- Use the fact that 1 + abs b ≤ 1 + (abs a + abs b) to show the inequality
      have h₁₈ : 1 + abs b ≤ 1 + (abs a + abs b) := by
        nlinarith [h₅]
      -- Use the division inequality to prove the result
      have h₁₉ : abs b / (1 + (abs a + abs b)) ≤ abs b / (1 + abs b) := by
        apply div_le_div_of_le_left (by positivity) (by positivity)
        <;> nlinarith
      exact h₁₉
    have h₂₀ : abs a / (1 + (abs a + abs b)) + abs b / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
      linarith
    linarith
  
  have h₅ : abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    calc
      abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + (abs a + abs b)) := h₃
      _ ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := h₄
  
  exact h₅