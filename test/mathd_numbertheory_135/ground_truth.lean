import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_135
  (n A B C : ℕ)
  (h₀ : n = 3^17 + 3^10)
  (h₁ : 11 ∣ (n + 1))
  (h₂ : [A,B,C].Pairwise (·≠·))
  (h₃ : {A,B,C} ⊂ Finset.Icc 0 9)
  (h₄ : Odd A ∧ Odd C)
  (h₅ : ¬ 3 ∣ B)
  (h₆ : Nat.digits 10 n = [B,A,B,C,C,A,C,B,A]) :
  100 * A + 10 * B + C = 129 := by
  have h₇ : n = 129199212 := by
    rw [h₀]
    norm_num
    <;> rfl
  
  have h₈ : B = 2 := by
    rw [h₇] at h₆
    norm_num [Nat.digits_len] at h₆ <;>
    (try omega) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        simp_all [Finset.ext_iff, Finset.mem_Icc, List.Pairwise]
        <;> omega
      }) <;>
    (try
      {
        norm_num at h₆ ⊢
        <;> aesop
      })
    <;>
    (try
      {
        rcases h₄ with ⟨h₄₁, h₄₂⟩
        cases' h₄₁ with k hk <;> cases' h₄₂ with m hm <;> omega
      })
    <;>
    (try
      {
        omega
      })
  
  have h₉ : A = 1 := by
    rw [h₇] at h₆
    norm_num [Nat.digits_len] at h₆ <;>
    (try omega) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        simp_all [Finset.ext_iff, Finset.mem_Icc, List.Pairwise]
        <;> omega
      }) <;>
    (try
      {
        norm_num at h₆ ⊢
        <;> aesop
      })
    <;>
    (try
      {
        rcases h₄ with ⟨h₄₁, h₄₂⟩
        cases' h₄₁ with k hk <;> cases' h₄₂ with m hm <;> omega
      })
    <;>
    (try
      {
        omega
      })
  
  have h₁₀ : C = 9 := by
    rw [h₇] at h₆
    norm_num [Nat.digits_len] at h₆ <;>
    (try omega) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        simp_all [Finset.ext_iff, Finset.mem_Icc, List.Pairwise]
        <;> omega
      }) <;>
    (try
      {
        norm_num at h₆ ⊢
        <;> aesop
      })
    <;>
    (try
      {
        rcases h₄ with ⟨h₄₁, h₄₂⟩
        cases' h₄₁ with k hk <;> cases' h₄₂ with m hm <;> omega
      })
    <;>
    (try
      {
        omega
      })
  
  have h₁₁ : 100 * A + 10 * B + C = 129 := by
    rw [h₉, h₈, h₁₀]
    <;> norm_num
    <;> aesop
  
  apply h₁₁