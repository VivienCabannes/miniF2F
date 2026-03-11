import Mathlib
import Aesop
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 400000
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial

lemma round1_h_sum1998 (u : ℕ → ℕ)
  (h₀ : u 0 = 4)
  (h₁ : u 1 = 7)
  (h₂ : ∀ n : ℕ, u (n + 2) = (u n + u (n + 1)) % 10):
  ∑ k in Finset.range 1998, u k = 9996 := by
  have hu2 : u 2 = 1 := by
    have h21 : u 2 = (u 0 + u 1) % 10 := h₂ 0
    norm_num [h₀, h₁] at h21 ⊢
    <;> omega
  have hu3 : u 3 = 8 := by
    have h31 : u 3 = (u 1 + u 2) % 10 := h₂ 1
    norm_num [h₁, hu2] at h31 ⊢
    <;> omega
  have hu4 : u 4 = 9 := by
    have h41 : u 4 = (u 2 + u 3) % 10 := h₂ 2
    norm_num [hu2, hu3] at h41 ⊢
    <;> omega
  have hu5 : u 5 = 7 := by
    have h51 : u 5 = (u 3 + u 4) % 10 := h₂ 3
    norm_num [hu3, hu4] at h51 ⊢
    <;> omega
  have hu6 : u 6 = 6 := by
    have h61 : u 6 = (u 4 + u 5) % 10 := h₂ 4
    norm_num [hu4, hu5] at h61 ⊢
    <;> omega
  have hu7 : u 7 = 3 := by
    have h71 : u 7 = (u 5 + u 6) % 10 := h₂ 5
    norm_num [hu5, hu6] at h71 ⊢
    <;> omega
  have hu8 : u 8 = 9 := by
    have h81 : u 8 = (u 6 + u 7) % 10 := h₂ 6
    norm_num [hu6, hu7] at h81 ⊢
    <;> omega
  have hu9 : u 9 = 2 := by
    have h91 : u 9 = (u 7 + u 8) % 10 := h₂ 7
    norm_num [hu7, hu8] at h91 ⊢
    <;> omega
  have hu10 : u 10 = 1 := by
    have h101 : u 10 = (u 8 + u 9) % 10 := h₂ 8
    norm_num [hu8, hu9] at h101 ⊢
    <;> omega
  have hu11 : u 11 = 3 := by
    have h111 : u 11 = (u 9 + u 10) % 10 := h₂ 9
    norm_num [hu9, hu10] at h111 ⊢
    <;> omega
  have hu12 : u 12 = 4 := by
    have h121 : u 12 = (u 10 + u 11) % 10 := h₂ 10
    norm_num [hu10, hu11] at h121 ⊢
    <;> omega
  have hu13 : u 13 = 7 := by
    have h131 : u 13 = (u 11 + u 12) % 10 := h₂ 11
    norm_num [hu11, hu12] at h131 ⊢
    <;> omega
  have h_period : ∀ k, u (k + 12) = u k := by
    have h : ∀ k, u (k + 12) = u k ∧ u (k + 1 + 12) = u (k + 1) := by
      intro k
      induction k with
      | zero =>
        constructor <;> norm_num [h₀, h₁, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, hu10, hu11, hu12, hu13] <;> aesop
      | succ k ih =>
        have h1 : u (k + 1 + 12) = u (k + 1) := ih.2
        have h2 : u (k + 2 + 12) = u (k + 2) := by
          have h21 : u (k + 2 + 12) = (u (k + 12) + u (k + 1 + 12)) % 10 := by
            have h : u ((k + 12) + 2) = (u (k + 12) + u (k + 1 + 12)) % 10 := by
              simpa using h₂ (k + 12)
            have h22 : k + 2 + 12 = (k + 12) + 2 := by ring
            rw [h22]
            exact h
          have h22 : u (k + 12) = u k := ih.1
          have h23 : u (k + 1 + 12) = u (k + 1) := ih.2
          have h24 : u (k + 2) = (u k + u (k + 1)) % 10 := by simpa using h₂ k
          rw [h21, h22, h23, h24]
          <;> simp [Nat.add_assoc]
          <;> ring_nf
        constructor
        · exact h1
        · simpa using h2
    intro k
    have h14 := (h k).1
    linarith
  have h_sum12 : ∑ k in Finset.range 12, u k = 60 := by
    simp [Finset.sum_range_succ, h₀, h₁, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, hu10, hu11]
    <;> norm_num
    <;> aesop
  have h_sum_add_12 : ∀ n, ∑ k in Finset.range (n + 12), u k = ∑ k in Finset.range n, u k + ∑ k in Finset.range 12, u k := by
    intro n
    induction n with
    | zero =>
      simp [Finset.sum_range_succ]
      <;> aesop
    | succ n ih =>
      have h1 : ∑ k in Finset.range ((n + 1) + 12), u k = (∑ k in Finset.range (n + 12), u k) + u (n + 12) := by
        simp [Finset.sum_range_succ, add_assoc]
        <;> ring_nf
      have h2 : ∑ k in Finset.range (n + 1), u k = (∑ k in Finset.range n, u k) + u n := by
        simp [Finset.sum_range_succ, add_assoc]
        <;> ring_nf
      have h3 : u (n + 12) = u n := by
        have h31 := h_period n
        ring_nf at h31 ⊢
        <;> linarith
      rw [h1, h2] at *
      linarith
  have h_sum_add_12_60 : ∀ n, ∑ k in Finset.range (n + 12), u k = ∑ k in Finset.range n, u k + 60 := by
    intro n
    have h4 := h_sum_add_12 n
    rw [h_sum12] at h4
    linarith
  have h_sum_6_12m : ∀ m, ∑ k in Finset.range (6 + 12 * m), u k = ∑ k in Finset.range 6, u k + 60 * m := by
    intro m
    induction m with
    | zero =>
      simp [Finset.sum_range_succ]
      <;> ring_nf
      <;> aesop
    | succ m ih =>
      have h5 : ∑ k in Finset.range (6 + 12 * (m + 1)), u k = ∑ k in Finset.range ((6 + 12 * m) + 12), u k := by
        have h51 : 6 + 12 * (m + 1) = (6 + 12 * m) + 12 := by
          ring
        rw [h51]
        <;> aesop
      have h6 : ∑ k in Finset.range ((6 + 12 * m) + 12), u k = ∑ k in Finset.range (6 + 12 * m), u k + 60 := by
        specialize h_sum_add_12_60 (6 + 12 * m)
        simpa using h_sum_add_12_60
      rw [h5, h6]
      rw [ih]
      simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
      <;> ring_nf at *
      <;> linarith
  have h_sum6 : ∑ k in Finset.range 6, u k = 36 := by
    simp [Finset.sum_range_succ, h₀, h₁, hu2, hu3, hu4, hu5]
    <;> norm_num
    <;> aesop
  have h_final : ∑ k in Finset.range 1998, u k = 9996 := by
    have h9 := h_sum_6_12m 166
    norm_num [h_sum6] at h9 ⊢
    <;> linarith
  exact h_final

theorem amc12a_2002_p21 (u : ℕ → ℕ) (h₀ : u 0 = 4) (h₁ : u 1 = 7) (h₂ : ∀ n : ℕ, u (n + 2) = (u n + u (n + 1)) % 10) : ∀ n, (∑ k in Finset.range n, u k) > 10000 → 1999 ≤ n := by

  have h8 : ∑ k in Finset.range 1998, u k = 9996 := round1_h_sum1998 u h₀ h₁ h₂
  intro n h
  by_contra h3
  have h4 : n ≤ 1998 := by linarith
  have h10 : ∑ k in Finset.range n, u k ≤ ∑ k in Finset.range 1998, u k := by
    have h5 : Finset.range n ⊆ Finset.range 1998 := by
      apply Finset.range_subset.2
      linarith
    have h6 : ∀ k, 0 ≤ u k := by
      intro k
      simp
    have h7 : ∑ k in Finset.range n, u k ≤ ∑ k in Finset.range 1998, u k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact h5
      · intro i _ _
        exact Nat.zero_le (u i)
    linarith
  linarith [h8, h10, h]
