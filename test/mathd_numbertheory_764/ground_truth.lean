import Mathlib

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_764
  (p : ℕ)
  (h₀ : Nat.Prime p)
  (h₁ : 7 ≤ p) :
  ∑ k ∈ Finset.Icc 1 (p-2), ((k: ZMod p)⁻¹ * ((k: ZMod p) + 1)⁻¹) = 2 := by
  have hp : Fact (Nat.Prime p) := ⟨h₀⟩
  have hp2 : 2 < p := by omega
  -- For k ∈ {1,...,p-2}, k and k+1 are nonzero in ZMod p
  have hk_ne : ∀ k ∈ Finset.Icc 1 (p-2), (k : ZMod p) ≠ 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
    omega
  have hk1_ne : ∀ k ∈ Finset.Icc 1 (p-2), ((k : ZMod p) + 1) ≠ 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [show (k : ZMod p) + 1 = ((k + 1 : ℕ) : ZMod p) from by push_cast; ring]
    rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
    omega
  -- Partial fractions: k⁻¹ * (k+1)⁻¹ = k⁻¹ - (k+1)⁻¹
  conv_lhs => ext k; rw [show ((k : ZMod p))⁻¹ * ((k : ZMod p) + 1)⁻¹ =
    (k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹ from by sorry]
  -- Telescoping: ∑_{k=1}^{p-2} (k⁻¹ - (k+1)⁻¹) = 1⁻¹ - (p-1)⁻¹
  sorry
