import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1983_p3
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (x^2 + (18 * x +  30) - 2 * Real.sqrt (x^2 + (18 * x + 45))))
  (h₁ : Fintype (f⁻¹' {0})) :
  ∏ x ∈ (f⁻¹' {0}).toFinset, x = 20 := by
  have h₂ : (-9 + Real.sqrt 61) ∈ f ⁻¹' {0} := by
    have h₂₁ : f (-9 + Real.sqrt 61) = 0 := by
      rw [h₀]
      have h₂₂ : Real.sqrt ((-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)) = 5 := by
        have h₂₃ : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45) = 25 := by
          nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
        rw [h₂₃, show (25 : ℝ) = 5 ^ 2 from by norm_num]
        exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)
      rw [h₂₂]
      nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
    have h₂₃ : f (-9 + Real.sqrt 61) = 0 := h₂₁
    have h₂₄ : (-9 + Real.sqrt 61) ∈ f ⁻¹' {0} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact h₂₃
    exact h₂₄
  
  have h₃ : (-9 - Real.sqrt 61) ∈ f ⁻¹' {0} := by
    have h₃₁ : f (-9 - Real.sqrt 61) = 0 := by
      rw [h₀]
      have h₃₂ : Real.sqrt ((-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)) = 5 := by
        have h₃₃ : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45) = 25 := by
          nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
        rw [h₃₃, show (25 : ℝ) = 5 ^ 2 from by norm_num]
        exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)
      rw [h₃₂]
      nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
    have h₃₄ : f (-9 - Real.sqrt 61) = 0 := h₃₁
    have h₃₅ : (-9 - Real.sqrt 61) ∈ f ⁻¹' {0} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact h₃₄
    exact h₃₅
  
  have h₄ : ∀ (x : ℝ), x ∈ f ⁻¹' {0} → x = (-9 + Real.sqrt 61) ∨ x = (-9 - Real.sqrt 61) := by
    intro x hx
    have h₅ : f x = 0 := by simpa using hx
    have h₆ : f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) := by rw [h₀]
    rw [h₆] at h₅
    have h₇ : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := by linarith
    have h₈ : x ^ 2 + (18 * x + 30) = 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) := by linarith
    have h₉ : x ^ 2 + (18 * x + 45) ≥ 0 := by
      by_contra h
      have h₁₀ : Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := by
        rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
      rw [h₁₀] at h₈
      nlinarith
    have h₁₀ : Real.sqrt (x ^ 2 + (18 * x + 45)) ≥ 0 := Real.sqrt_nonneg _
    have h₁₁ : x ^ 2 + (18 * x + 45) ≥ 0 := by linarith
    have h₁₂ : Real.sqrt (x ^ 2 + (18 * x + 45)) ^ 2 = x ^ 2 + (18 * x + 45) := by
      rw [Real.sq_sqrt] <;> linarith
    have h₁₃ : (x ^ 2 + (18 * x + 30)) ^ 2 = 4 * (x ^ 2 + (18 * x + 45)) := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x ^ 2 + (18 * x + 45))]
    have h₁₄ : x ^ 2 + 18 * x + 20 = 0 := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x ^ 2 + (18 * x + 45))]
    have h₁₅ : x = -9 + Real.sqrt 61 ∨ x = -9 - Real.sqrt 61 := by
      have h₁₆ : x = -9 + Real.sqrt 61 ∨ x = -9 - Real.sqrt 61 := by
        apply or_iff_not_imp_left.mpr
        intro h₁₇
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₇)
        nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
      exact h₁₆
    cases h₁₅ with
    | inl h₁₅ =>
      exact Or.inl h₁₅
    | inr h₁₅ =>
      exact Or.inr h₁₅
  
  have h₅ : (f ⁻¹' {0}).toFinset = { -9 + Real.sqrt 61, -9 - Real.sqrt 61 } := by
    apply Finset.ext
    intro x
    simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h₅₁ : x = (-9 + Real.sqrt 61) ∨ x = (-9 - Real.sqrt 61) := h₄ x h
      cases h₅₁ with
      | inl h₅₁ =>
        simp [h₅₁]
        <;>
        (try norm_num) <;>
        (try ring_nf at * <;> norm_num at * <;> nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]) <;>
        (try aesop)
      | inr h₅₁ =>
        simp [h₅₁]
        <;>
        (try norm_num) <;>
        (try ring_nf at * <;> norm_num at * <;> nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]) <;>
        (try aesop)
    · intro h
      have h₅₂ : x = -9 + Real.sqrt 61 ∨ x = -9 - Real.sqrt 61 := by aesop
      cases h₅₂ with
      | inl h₅₂ =>
        rw [h₅₂]
        exact by simpa using h₂
      | inr h₅₂ =>
        rw [h₅₂]
        exact by simpa using h₃
  
  have h₆ : (∏ x ∈ (f ⁻¹' {0}).toFinset, x) = 20 := by
    rw [h₅]
    have h₆₁ : ∏ x ∈ ({ -9 + Real.sqrt 61, -9 - Real.sqrt 61 } : Finset ℝ), x = 20 := by
      have h₆₂ : ∏ x ∈ ({ -9 + Real.sqrt 61, -9 - Real.sqrt 61 } : Finset ℝ), x = ((-9 + Real.sqrt 61) * (-9 - Real.sqrt 61)) := by
        simp [Finset.prod_pair (show (-9 + Real.sqrt 61 : ℝ) ≠ -9 - Real.sqrt 61 by
          intro h
          nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)])]
        <;>
        ring_nf <;>
        norm_num <;>
        nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
      rw [h₆₂]
      have h₆₃ : ((-9 + Real.sqrt 61) * (-9 - Real.sqrt 61) : ℝ) = 20 := by
        nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
      rw [h₆₃]
      <;>
      norm_num
    rw [h₆₁]
    <;>
    norm_num
  
  exact h₆