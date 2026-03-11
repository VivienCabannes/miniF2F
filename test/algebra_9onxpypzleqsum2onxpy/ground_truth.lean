import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x + y := by linarith
  have h₂ : 0 < y + z := by linarith
  have h₃ : 0 < z + x := by linarith
  have h₄ : 0 < x + y + z := by linarith
  have h₅ : 0 < (x + y) * (y + z) * (z + x) := by positivity
  have h₆ : 0 < (x + y) * (y + z) := by positivity
  have h₇ : 0 < (y + z) * (z + x) := by positivity
  have h₈ : 0 < (z + x) * (x + y) := by positivity
  have h₉ : 2 * (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 9 := by
    have h₉₁ : 0 < x + y := by linarith
    have h₉₂ : 0 < y + z := by linarith
    have h₉₃ : 0 < z + x := by linarith
    have h₉₄ : 0 < (x + y) * (y + z) := by positivity
    have h₉₅ : 0 < (y + z) * (z + x) := by positivity
    have h₉₆ : 0 < (z + x) * (x + y) := by positivity
    field_simp [h₉₁.ne', h₉₂.ne', h₉₃.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y - y - z), sq_nonneg (y + z - z - x), sq_nonneg (z + x - x - y)]
  
  have h₁₀ : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 9 / (2 * (x + y + z)) := by
    have h₁₀₁ : 0 < x + y + z := by linarith
    have h₁₀₂ : 0 < 2 * (x + y + z) := by positivity
    have h₁₀₃ : 0 < x + y := by linarith
    have h₁₀₄ : 0 < y + z := by linarith
    have h₁₀₅ : 0 < z + x := by linarith
    -- Use the given inequality to derive the desired result
    calc
      (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 9 / (2 * (x + y + z)) := by
        -- Use the given inequality to derive the desired result
        have h₁₀₆ : 2 * (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 9 := by
          simpa [add_assoc] using h₉
        calc
          (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) = (2 * (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x))) / (2 * (x + y + z)) := by
            field_simp [h₁₀₁.ne', h₁₀₂.ne']
            <;> ring
            <;> field_simp [h₁₀₁.ne', h₁₀₂.ne']
            <;> ring
          _ ≥ 9 / (2 * (x + y + z)) := by
            -- Use the given inequality to derive the desired result
            rw [ge_iff_le]
            rw [div_le_div_iff (by positivity) (by positivity)]
            nlinarith
      _ = 9 / (2 * (x + y + z)) := by rfl
  
  have h₁₁ : (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) ≥ 9 / (x + y + z) := by
    have h₁₁₁ : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) = 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
      ring
    rw [h₁₁₁]
    have h₁₁₂ : 9 / (x + y + z) = 2 * (9 / (2 * (x + y + z))) := by
      field_simp [h₄.ne']
      <;> ring
      <;> field_simp [h₄.ne']
      <;> ring
    rw [h₁₁₂]
    have h₁₁₃ : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) ≥ 9 / (2 * (x + y + z)) := by
      linarith
    nlinarith
  
  have h₁₂ : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    linarith
  
  exact h₁₂