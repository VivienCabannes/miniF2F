import Mathlib

open BigOperators Real Nat Topology Rat

theorem numbertheory_notEquiv2i2jasqbsqdiv8 :
  ¬ (∀ a b : ℤ, (∃ i j, a = 2*i ∧ b=2*j) ↔ (∃ k, a^2 + b^2 = 8*k)) := by
  intro h
  have h1 := (h 2 0).mp ⟨1, 0, rfl, rfl⟩
  obtain ⟨k, hk⟩ := h1
  omega
