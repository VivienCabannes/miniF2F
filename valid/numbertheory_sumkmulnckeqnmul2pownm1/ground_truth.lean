import Mathlib

open BigOperators Real Nat Topology Rat

theorem numbertheory_sumkmulnckeqnmul2pownm1 (n : ℕ) (h₀ : 0 < n) :
  (∑ k ∈ Finset.Icc 1 n, k * Nat.choose n k) = n * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one]
  rw [show Finset.Icc 1 (m + 1) = (Finset.range (m + 1)).map
    ⟨fun i => i + 1, Nat.succ_injective⟩ from by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨by omega, by omega⟩]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have key : ∀ i ∈ Finset.range (m + 1),
      (i + 1) * Nat.choose (m + 1) (i + 1) = (m + 1) * Nat.choose m i := by
    intro i _
    have h := Nat.succ_mul_choose_eq m i
    linarith
  rw [Finset.sum_congr rfl key]
  rw [← Finset.mul_sum]
  congr 1
  exact Nat.sum_range_choose m
