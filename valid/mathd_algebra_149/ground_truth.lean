import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_149 (f : ℝ → ℝ) (h₀ : ∀ x < -5, f x = x ^ 2 + 5)
  (h₁ : ∀ x ≥ -5, f x = 3 * x - 8) (h₂ : Fintype (f ⁻¹' {10})) :
  (∑ k ∈ (f ⁻¹' {10}).toFinset, k) = 6 := by
  have case1 : ∀ x < -5, f x = x ^ 2 + 5 := by
    intro x hx
    -- We need to show that for x < -5, f(x) = x^2 + 5.
    -- Since f(x) is defined as x^2 + 5 for all x < -5, we can directly apply this definition.
    apply h₀
    exact hx
  
  have case2 : ∀ x ≥ -5, f x = 3 * x - 8 := by
    intro x hx
    have h₃ := h₁ x hx
    simp_all
  
  have no_solutions_case1 : ∀ x < -5, f x ≠ 10 := by
    intro x hx
    simp_all [lt_irrefl]
    <;> nlinarith
    <;> linarith
    <;> nlinarith
    <;> linarith
    <;> nlinarith
    <;> linarith
    <;> nlinarith
    <;> linarith
  
  have solution_case2 : ∃! x ≥ -5, f x = 10 := by
    -- We use the second piece of the function definition for x ≥ -5, as x < -5 yields no solutions.
    refine' ⟨(10 + 8) / 3, by norm_num [h₁], fun a ha => _⟩
    -- We need to show that a must be equal to (10 + 8) / 3 if it satisfies f(a) = 10 and a ≥ -5.
    have h₃ := h₁ a ha.1
    -- Simplify the equation f(a) = 10 using the second piece of the function definition.
    simp_all
    -- Solve the equation for a using basic arithmetic operations.
    <;> linarith
  
  have sum_of_solutions : (∑ k in (f ⁻¹' {10}).toFinset, k) = 6 := by
    have : f ⁻¹' {10} = {6} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · intro h
        match lt_or_le x (-5) with
        | .inl hlt =>
          rw [case1 x hlt] at h
          -- For x < -5, f(x) = x^2 + 5. We solve x^2 + 5 = 10.
          nlinarith
        | .inr hge =>
          rw [case2 x hge] at h
          -- For x ≥ -5, f(x) = 3x - 8. We solve 3x - 8 = 10.
          linarith
      · intro h
        rw [h]
        -- Verify that f(6) = 10.
        rw [case2 6 (by norm_num)]  -- Since 6 ≥ -5, we use f(x) = 3x - 8.
        norm_num
    simp [this]
  
  simpa [sum_of_solutions] using sum_of_solutions