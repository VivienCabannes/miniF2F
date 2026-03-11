import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem numbertheory_sumkmulnckeqnmul2pownm1 (n : ℕ) (h₀ : 0 < n) :
  (∑ k ∈ Finset.Icc 1 n, k * Nat.choose n k) = n * 2 ^ (n - 1) := by
  have h1 : ∀ k ∈ Finset.Icc 1 n, k * Nat.choose n k = Nat.choose n k * k := by
    intro k hk
    simp [Nat.mul_comm, h₀] at hk ⊢
    -- The `simp` tactic is used to simplify the context and ensure that the multiplication is commutative.
    -- The `Nat.mul_comm` lemma is used to commute the multiplication, and `h₀` ensures that the context is valid.
    <;>
    simp_all [Finset.mem_Icc, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    -- The `simp_all` tactic is used to simplify all hypotheses and the goal, ensuring that the context is clear and concise.
    -- The `Finset.mem_Icc` lemma is used to ensure that the element `k` is within the range `[1, n]`.
    <;>
    norm_num
    -- The `norm_num` tactic is used to normalize numerical expressions, ensuring that the arithmetic is correct.
    <;>
    omega
  
  have h2 : ∑ k in Finset.Icc 1 n, k * Nat.choose n k = ∑ k in Finset.Icc 1 n, Nat.choose n k * k := by
    refine' Finset.sum_congr rfl fun k hk => _
    have hk' := h1 k hk
    simp_all [Nat.mul_comm]
    -- We use the commutativity of multiplication to show that the sums are equal by pairwise equal terms.
    -- The term k * choose n k is equal to choose n k * k by the commutativity of multiplication.
    -- Therefore, each term in the first sum is equal to the corresponding term in the second sum.
    -- This establishes the equality of the sums.
    <;> ring_nf
    <;> simp_all [Finset.sum_congr]
    <;> apply congr_arg
    <;> apply congr_arg
    <;> apply Finset.sum_congr
    <;> simp_all
  
  have h3 : ∀ k ∈ Finset.Icc 1 n, Nat.choose n k * k = n * Nat.choose (n - 1) (k - 1) := by
    intro k hk
    have hh₁ : 0 < n := h₀
    have hh₂ : 0 < k := by
      have h₁ : k ∈ Finset.Icc 1 n := hk
      have h₂ : 1 ≤ k := by
        rw [Finset.mem_Icc] at h₁
        exact h₁.1
      linarith
    have hh₃ : k ≤ n := by
      have h₁ : k ∈ Finset.Icc 1 n := hk
      have h₂ : k ≤ n := by
        rw [Finset.mem_Icc] at h₁
        exact h₁.2
      exact h₂
    calc
      Nat.choose n k * k = n * Nat.choose (n - 1) (k - 1) := by
        -- Use the property of binomial coefficients and combinatorial reasoning to show the equality
        have h₁ : k ≤ n := hh₃
        have h₂ : 0 < k := hh₂
        have h₃ : 0 < n := hh₁
        rw [← Nat.succ_pred_eq_of_pos h₂]
        rw [← Nat.succ_pred_eq_of_pos h₃]
        -- Use the combinatorial identity and simplify the expression
        simp_all [Nat.choose_succ_succ, Nat.succ_mul_choose_eq]
      _ = n * Nat.choose (n - 1) (k - 1) := by rfl
  have h4 : ∑ k in Finset.Icc 1 n, Nat.choose n k * k = ∑ k in Finset.Icc 1 n, n * Nat.choose (n - 1) (k - 1) := by
    rw [Finset.sum_congr rfl (fun k hk => h3 k hk)]
    -- Using the given property h3, we substitute n * Nat.choose (n - 1) (k - 1) for each term in the sum.
    <;> simp_all [Finset.mul_sum]
    -- Simplify the expression using the properties of sums and multiplication.
    <;> ring
    -- Use algebraic simplification to show that the sums are equal.
    <;> linarith
  
  have h5 : ∑ k in Finset.Icc 1 n, n * Nat.choose (n - 1) (k - 1) = n * ∑ k in Finset.Icc 1 n, Nat.choose (n - 1) (k - 1) := by
    rw [Finset.mul_sum]
    <;> simp_all [Finset.sum_mul]
    <;> apply Eq.refl
  
  have h6 : ∑ k in Finset.Icc 1 n, Nat.choose (n - 1) (k - 1) = ∑ j in Finset.Icc 0 (n - 1), Nat.choose (n - 1) j := by
    -- We use the fact that the sum of binomial coefficients over a shifted range can be transformed into a sum over a standard range.
    have h6 : ∀ k ∈ Finset.Icc 1 n, k - 1 ∈ Finset.Icc 0 (n - 1) := by
      intro k hk
      simp_all [Finset.mem_Icc, Nat.succ_le_iff, Nat.sub_le]
      <;> omega
    -- We use the fact that the sum of binomial coefficients over a shifted range can be transformed into a sum over a standard range.
    have h7 : ∑ k in Finset.Icc 1 n, Nat.choose (n - 1) (k - 1) = ∑ j in Finset.Icc 0 (n - 1), Nat.choose (n - 1) j := by
      apply Finset.sum_bij' (fun k hk => k - 1) (fun j hj => j + 1)
      <;> simp_all [Finset.mem_Icc, Nat.succ_le_iff, Nat.sub_le]
      <;> omega
    -- The final result follows from the established equality.
    exact h7
  have h7 : ∑ j in Finset.Icc 0 (n - 1), Nat.choose (n - 1) j = 2 ^ (n - 1) := by
    have h7 : ∑ j in Finset.Icc 0 (n - 1), Nat.choose (n - 1) j = 2 ^ (n - 1) := by
      rw [← Nat.sum_range_choose]
      congr
      ext j
      simp [Finset.mem_Icc, Nat.choose_symm]
      <;> omega
    simp_all
  
  have h8 : n * ∑ j in Finset.Icc 0 (n - 1), Nat.choose (n - 1) j = n * 2 ^ (n - 1) := by
    simp [Nat.choose_eq_factorial_div_factorial] at h1 h3 h5 h6 h7 ⊢
    -- Simplify the given identities using the combination formula and the properties of sums and products.
    <;> simp_all [Finset.sum_mul, Finset.mul_sum, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    -- Apply the properties of sums and products to show the desired equality.
    <;> linarith
  
  have h9 : ∑ k in Finset.Icc 1 n, k * Nat.choose n k = n * 2 ^ (n - 1) := by
    have h9 := h2
    have h10 := h4
    have h11 := h5
    have h12 := h6
    have h13 := h7
    have h14 := h8
    simp_all [Finset.sum_mul, Finset.mul_sum, mul_comm]
    <;> ring_nf <;> simp_all [Finset.sum_mul, Finset.mul_sum, mul_comm]
    <;> linarith
  
  rw [h9]
  <;> simp_all [Finset.sum_Icc_succ_top]
  <;> linarith