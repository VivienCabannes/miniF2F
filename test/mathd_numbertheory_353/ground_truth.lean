import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_353
  (s : ℕ)
  (h₀ : s = ∑ k ∈ Finset.Icc 2010 4018, k) :
  s % 2009 = 0 := by
  have h₁ : s = 2009 * 3014 := by
    rw [h₀]
    -- Reindex the sum to use the formula for the sum of consecutive integers
    have h₂ : (∑ k in Finset.Icc 2010 4018, k) = ∑ t in Finset.range 2009, (t + 2010) := by
      -- Prove that the image of the range 2009 under (· + 2010) is Icc 2010 4018
      have h₃ : Finset.Icc 2010 4018 = (Finset.range 2009).image (fun t => t + 2010) := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro hx
          -- Prove that if x is in Icc 2010 4018, then x is in the image of the range
          have h₄ : 2010 ≤ x ∧ x ≤ 4018 := hx
          have h₅ : x ≥ 2010 := by linarith
          have h₆ : x ≤ 4018 := by linarith
          have h₇ : x - 2010 < 2009 := by omega
          use x - 2010
          <;> simp_all [Nat.sub_add_cancel]
          <;> omega
        · intro hx
          -- Prove that if x is in the image of the range, then x is in Icc 2010 4018
          rcases hx with ⟨t, ht₁, ht₂⟩
          have h₄ : t < 2009 := ht₁
          have h₅ : t + 2010 = x := by omega
          have h₆ : 2010 ≤ x := by omega
          have h₇ : x ≤ 4018 := by omega
          exact ⟨by omega, by omega⟩
      rw [h₃]
      -- Use the sum_image lemma to rewrite the sum
      rw [Finset.sum_image]
      <;> simp_all [Function.Injective]
      <;> omega
    rw [h₂]
    -- Compute the sum of (t + 2010) for t in range 2009
    have h₃ : (∑ t in Finset.range 2009, (t + 2010 : ℕ)) = (∑ t in Finset.range 2009, t) + ∑ t in Finset.range 2009, 2010 := by
      rw [Finset.sum_add_distrib]
    rw [h₃]
    -- Compute the sum of t for t in range 2009
    have h₄ : (∑ t in Finset.range 2009, t) = 2009 * 1004 := by
      -- Use the formula for the sum of the first n natural numbers
      rw [Finset.sum_range_id]
      <;> norm_num
      <;> ring_nf
      <;> norm_num
    -- Compute the sum of 2010 for t in range 2009
    have h₅ : (∑ t in Finset.range 2009, (2010 : ℕ)) = 2009 * 2010 := by
      simp [Finset.sum_const, Finset.card_range]
      <;> ring_nf
    -- Combine the results
    rw [h₄, h₅]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
  
  have h₂ : s % 2009 = 0 := by
    rw [h₁]
    <;> norm_num
    <;> rfl
  
  exact h₂