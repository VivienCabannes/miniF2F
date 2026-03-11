import Mathlib

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_764
  (p : ℕ)
  (h₀ : Nat.Prime p)
  (h₁ : 7 ≤ p) :
  ∑ k ∈ Finset.Icc 1 (p-2), ((k: ZMod p)⁻¹ * ((k: ZMod p) + 1)⁻¹) = 2 := by
  haveI hp : Fact (Nat.Prime p) := ⟨h₀⟩
  have hp2 : 2 < p := by omega
  -- For k ∈ {1,...,p-2}, both k and k+1 are nonzero in ZMod p
  have hk_ne : ∀ k ∈ Finset.Icc 1 (p-2), (k : ZMod p) ≠ 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
  have hk1_ne : ∀ k ∈ Finset.Icc 1 (p-2), ((k : ZMod p) + 1) ≠ 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [show (k : ZMod p) + 1 = ((k + 1 : ℕ) : ZMod p) from by push_cast; ring]
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
  -- Partial fractions: k⁻¹ * (k+1)⁻¹ = k⁻¹ - (k+1)⁻¹ in ZMod p (a field)
  have partial_frac : ∀ k ∈ Finset.Icc 1 (p-2),
      ((k : ZMod p))⁻¹ * ((k : ZMod p) + 1)⁻¹ =
      (k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹ := by
    intro k hk
    have hk0 := hk_ne k hk
    have hk10 := hk1_ne k hk
    field_simp; ring
  -- Apply partial fractions and split into difference of sums
  rw [Finset.sum_congr rfl partial_frac, Finset.sum_sub_distrib]
  -- Reindex: ∑ k ∈ Icc 1 (p-2), ((k+1):ZMod p)⁻¹ = ∑ j ∈ Icc 2 (p-1), (j:ZMod p)⁻¹
  have reindex : ∑ k ∈ Finset.Icc 1 (p-2), ((k : ZMod p) + 1)⁻¹ =
      ∑ j ∈ Finset.Icc 2 (p-1), ((j : ZMod p))⁻¹ := by
    have hset : Finset.Icc 2 (p - 1) = (Finset.Icc 1 (p - 2)).map
        ⟨(· + 1), Nat.succ_injective⟩ := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩; exact ⟨by omega, by omega⟩
    rw [hset, Finset.sum_map]; congr 1; ext k
    simp only [Function.Embedding.coeFn_mk]
    congr 1; push_cast; ring
  rw [reindex]
  -- Split: Icc 1 (p-2) = {1} ∪ Icc 2 (p-2), Icc 2 (p-1) = {p-1} ∪ Icc 2 (p-2)
  have hsplit1 : Finset.Icc 1 (p - 2) = insert 1 (Finset.Icc 2 (p - 2)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hsplit2 : Finset.Icc 2 (p - 1) = insert (p - 1) (Finset.Icc 2 (p - 2)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit1, hsplit2]
  have h1_notin : (1 : ℕ) ∉ Finset.Icc 2 (p - 2) := by
    simp only [Finset.mem_Icc]; omega
  have hp1_notin : p - 1 ∉ Finset.Icc 2 (p - 2) := by
    simp only [Finset.mem_Icc]; omega
  rw [Finset.sum_insert h1_notin, Finset.sum_insert hp1_notin]
  -- The common sums over Icc 2 (p-2) cancel: (a + S) - (b + S) = a - b
  have cancel : ∀ (a b S : ZMod p), (a + S) - (b + S) = a - b := by intros; ring
  rw [cancel]
  -- Simplify: (1:ℕ)⁻¹ = 1
  simp only [Nat.cast_one, ZMod.inv_one p]
  -- (p-1 : ℕ) in ZMod p equals -1, since (p-1)+1 = p = 0 in ZMod p
  have hp1_eq : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have h1 : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
      rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) from by simp]
      rw [← Nat.cast_add, show p - 1 + 1 = p from by omega, ZMod.natCast_self]
    calc ((p - 1 : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) + 1 + (-1) := by ring
      _ = 0 + (-1) := by rw [h1]
      _ = -1 := by ring
  rw [hp1_eq, ZMod.inv_neg_one]
  -- 1 - (-1) = 2
  ring
