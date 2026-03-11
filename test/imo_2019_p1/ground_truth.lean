import Mathlib

open BigOperators Real Nat Topology Rat

theorem imo_2019_p1
  (f : ℤ → ℤ) :
  ((∀ a b, f (2 * a) + (2 * f b) = f (f (a + b))) ↔ (∀ z, f z = 0 \/ ∃ c, ∀ z, f z = 2 * z + c)) := by
  constructor
  · intro hf
    obtain ⟨m, H⟩ : ∃ m, ∀ b, f (b + 1) = f b + m := by
      refine ⟨(f 0 - f (-2)) / 2, fun b => ?_⟩
      refine sub_eq_iff_eq_add'.1 (Int.eq_ediv_of_mul_eq_right two_ne_zero ?_)
      have h1 : f 0 + 2 * f b = f (f b) := by simpa using hf 0 b
      have h2 : f (-2) + 2 * f (b + 1) = f (f b) := by simpa using hf (-1) (b + 1)
      linarith
    obtain ⟨c, H⟩ : ∃ c, ∀ b, f b = c + m * b := by
      refine ⟨f 0, fun b => ?_⟩
      induction b with
      | zero => simp
      | succ b ihb => simp [H, ihb, mul_add, add_assoc]
      | pred b ihb =>
        rw [← sub_eq_of_eq_add (H _)]
        simp [ihb]; ring
    have H3 : 2 * c = m * c := by simpa [H, mul_add] using hf 0 0
    obtain rfl | rfl : 2 = m ∨ m = 0 := by simpa [H, mul_add, H3] using hf 0 1
    · intro z; right; exact ⟨c, fun z => by simp [H, add_comm]⟩
    · intro z; left
      have := H z; simp at this
      have : c = 0 := by simpa [two_ne_zero] using H3
      simp [this] at H; exact H z
  · intro hfz a b
    by_cases h : ∀ z, f z = 0
    · simp [h]
    · push_neg at h
      obtain ⟨z₀, hz₀⟩ := h
      obtain (habs | ⟨c, hc⟩) := hfz z₀
      · exact absurd habs hz₀
      · simp [hc]; ring
