import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem amc12a_2020_p4
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ (d : ℕ), d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
  S.card = 100 := by
  -- The 4-digit numbers with all even digits and divisible by 5 are exactly
  -- those of the form 1000*a + 100*b + 10*c where a ∈ {2,4,6,8}, b,c ∈ {0,2,4,6,8}.
  -- Units digit must be 0 (only even digit divisible by 5).
  -- Thousands digit: {2,4,6,8} = 4 choices (can't be 0 for a 4-digit number).
  -- Middle digits: {0,2,4,6,8} = 5 choices each.
  -- Total = 4 × 5 × 5 × 1 = 100.
  --
  -- We show S equals a decidable filter on Finset.Icc 1000 9999,
  -- then use `decide` to verify the cardinality.
  have hS : S = (Finset.Icc 1000 9999).filter (fun n =>
    (∀ d ∈ Nat.digits 10 n, Even d) ∧ 5 ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hn
      obtain ⟨h1, h2, h3, h4⟩ := (h₀ n).mp hn
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · intro ⟨⟨h1, h2⟩, h3, h4⟩
      exact (h₀ n).mpr ⟨h1, h2, h3, h4⟩
  rw [hS]
  decide
