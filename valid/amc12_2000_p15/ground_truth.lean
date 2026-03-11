import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p15 (f : ℂ → ℂ) (h₀ : ∀ x, f (x / 3) = x ^ 2 + x + 1)
  (h₁ : Fintype (f ⁻¹' {7})) : (∑ y ∈ (f ⁻¹' {7}).toFinset, y / 3) = -1 / 9 := by
  have h₂ : ∀ y, f y = 9 * y^2 + 3 * y + 1 := by
    intro y
    have h₂ := h₀ (3 * y)
    simp [mul_assoc] at h₂
    have h₃ := h₀ (3 * y + 1)
    simp [mul_assoc] at h₃
    have h₄ := h₀ (3 * y - 1)
    simp [mul_assoc] at h₄
    -- Normalize the expressions to match the form of the final answer.
    ring_nf at h₂ h₃ h₄ ⊢
    -- Use linear arithmetic to conclude the proof.
    <;> simp_all [sub_eq_add_neg, add_assoc]
    <;> linarith
  
  have h₃ : ∀ y, f y = 7 ↔ 9 * y^2 + 3 * y - 6 = 0 := by
    intro y
    simp [h₂, sub_eq_zero, mul_comm]
    <;> ring_nf <;> norm_num
    <;> exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  
  have h₄ : (∑ y in (f ⁻¹' {7}).toFinset, y) = -1/3 := by
    have h₄ : f ⁻¹' {7} = {-1, 2/3} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · intro h
        have h₅ : f y = 7 := h
        have h₆ : 9 * y ^ 2 + 3 * y - 6 = 0 := by simpa [h₂, h₅] using h₃ y |>.mp h₅
        have h₇ : y = -1 ∨ y = 2 / 3 := by
          apply or_iff_not_imp_left.mpr
          intro h₈
          apply mul_left_cancel₀ (sub_ne_zero.mpr h₈)
          linear_combination h₆ / 9
        simp_all
      · intro h
        have h₅ : y = -1 ∨ y = 2 / 3 := h
        have h₆ : f y = 7 := by
          cases' h₅ with h₅ h₅
          · simp_all [h₂, h₅]
            norm_num
          · simp_all [h₂, h₅]
            norm_num
        exact h₆
    simp [h₄]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h₅ : (∑ y in (f ⁻¹' {7}).toFinset, y / 3) = -1/9 := by
    have h₅ : ∀ y, f y = 7 ↔ 9 * y ^ 2 + 3 * y - 6 = 0 := by simpa using h₃
    have h₆ : (∑ y in (f ⁻¹' {7}).toFinset, y) = -1/3 := by simpa using h₄
    have h₇ : (∑ y in (f ⁻¹' {7}).toFinset, y / 3) = (∑ y in (f ⁻¹' {7}).toFinset, y) / 3 := by
      simp [Finset.sum_div]
    rw [h₇, h₆]
    ring
  
  -- Normalize the numbers in the hypotheses and the goal.
  norm_num at h₀ h₂ h₃ h₄ h₅ ⊢
  -- Use linear arithmetic to prove the goal.
  <;> simp_all [Complex.ext_iff]
  <;> norm_num
  <;> linarith