import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem imo_1992_p1
  (p q r : ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (h₁ : (p - 1) * (q - 1) * (r - 1)∣(p * q * r - 1)) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  have h₂ : p ≥ 2 := by
    linarith [h₀.1]

  have h₃ : q ≥ 3 := by
    by_contra h
    have h₄ : q ≤ 2 := by linarith
    have h₅ : q ≥ 2 := by linarith [h₀.2.1]
    have h₆ : q = 2 := by linarith
    have h₇ : p < 2 := by linarith [h₀.2.1]
    have h₈ : p ≥ 2 := by linarith [h₀.1]
    linarith

  have h₄ : r ≥ 4 := by
    by_contra h
    have h₅ : r ≤ 3 := by linarith
    have h₆ : r ≥ 3 := by linarith [h₀.2.2]
    have h₇ : r = 3 := by linarith
    have h₈ : q < 3 := by linarith [h₀.2.2]
    have h₉ : q ≥ 3 := by linarith [h₃]
    linarith

  have h₅ : (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
    have h₆ : (p - 1 : ℤ) > 0 := by
      linarith
    have h₇ : (q - 1 : ℤ) > 0 := by
      linarith
    have h₈ : (r - 1 : ℤ) > 0 := by
      linarith
    have h₉ : (p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ) > 0 := by positivity
    have h₁₀ : ∃ (k : ℤ), (p * q * r - 1 : ℤ) = k * ((p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ)) := by
      obtain ⟨k, hk⟩ := h₁
      refine' ⟨k, _⟩
      linarith
    obtain ⟨k, hk⟩ := h₁₀
    have h₁₁ : k > 0 := by
      by_contra h₁₁
      have h₁₂ : k ≤ 0 := by linarith
      have h₁₃ : (p * q * r - 1 : ℤ) ≤ 0 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
          mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₄),
          mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₄)]
      have h₁₄ : (p * q * r : ℤ) ≤ 1 := by linarith
      have h₁₅ : (p : ℤ) ≥ 2 := by linarith
      have h₁₆ : (q : ℤ) ≥ 3 := by linarith
      have h₁₇ : (r : ℤ) ≥ 4 := by linarith
      have h₁₈ : (p * q * r : ℤ) ≥ 2 * 3 * 4 := by
        have h₁₉ : (p : ℤ) * q ≥ 2 * 3 := by nlinarith
        nlinarith
      linarith
    have h₁₂ : k ≤ 3 := by
      by_contra h₁₂
      have h₁₃ : k ≥ 4 := by linarith
      have h₁₄ : (p - 1 : ℤ) ≥ 1 := by
        linarith
      have h₁₅ : (q - 1 : ℤ) ≥ 2 := by
        linarith
      have h₁₆ : (r - 1 : ℤ) ≥ 3 := by
        linarith
      have h₁₇ : (p - 1 : ℤ) * (q - 1 : ℤ) ≥ 2 := by
        nlinarith
      have h₁₈ : (p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ) ≥ 6 := by
        nlinarith
      have h₁₉ : (k : ℤ) * ((p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ)) ≥ 4 * ((p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ)) := by
        nlinarith
      have h₂₀ : (p * q * r - 1 : ℤ) ≥ 4 * ((p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ)) := by
        linarith
      have h₂₁ : (p * q * r - 1 : ℤ) < 4 * ((p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ)) := by
        have h₂₂ : (p : ℤ) * q * r < 4 * ((p - 1 : ℤ) * (q - 1 : ℤ) * (r - 1 : ℤ)) + 1 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
            mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₄),
            mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₄)]
        linarith
      linarith
    have h₁₃ : k = 1 ∨ k = 2 ∨ k = 3 := by
      omega
    -- We need to handle each case of k separately
    rcases h₁₃ with (rfl | rfl | rfl)
    · -- Case k = 1
      have h₁₄ : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) := by
        ring_nf at hk ⊢
        <;> linarith
      have h₁₅ : p * q + p * r + q * r = p + q + r := by
        have h₁₅₁ : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) := by linarith
        ring_nf at h₁₅₁ ⊢
        nlinarith
      have h₁₆ : p = 2 := by
        by_contra h₁₆
        have h₁₇ : p ≥ 3 := by
          by_contra h₁₇
          have h₁₈ : p ≤ 2 := by linarith
          have h₁₉ : p = 2 := by linarith
          contradiction
        have h₂₀ : q ≥ 3 := by linarith
        have h₂₁ : r ≥ 4 := by linarith
        have h₂₂ : (p : ℤ) * q ≥ 3 * 3 := by
          nlinarith
        have h₂₃ : (p : ℤ) * r ≥ 3 * 4 := by
          nlinarith
        have h₂₄ : (q : ℤ) * r ≥ 3 * 4 := by
          nlinarith
        nlinarith
      have h₁₇ : q = 3 := by
        by_contra h₁₇
        have h₁₈ : q ≥ 4 := by
          by_contra h₁₈
          have h₁₉ : q ≤ 3 := by linarith
          have h₂₀ : q = 3 := by linarith
          contradiction
        have h₂₁ : p = 2 := by linarith
        have h₂₂ : (p : ℤ) * q ≥ 2 * 4 := by
          nlinarith
        have h₂₃ : (p : ℤ) * r ≥ 2 * 4 := by
          nlinarith
        have h₂₄ : (q : ℤ) * r ≥ 4 * 4 := by
          nlinarith
        nlinarith
      have h₁₈ : r = 4 := by
        by_contra h₁₈
        have h₁₉ : r ≥ 5 := by
          by_contra h₁₉
          have h₂₀ : r ≤ 4 := by linarith
          have h₂₁ : r = 4 := by linarith
          contradiction
        have h₂₂ : p = 2 := by linarith
        have h₂₃ : q = 3 := by linarith
        have h₂₄ : (p : ℤ) * q ≥ 2 * 3 := by
          nlinarith
        have h₂₅ : (p : ℤ) * r ≥ 2 * 5 := by
          nlinarith
        have h₂₆ : (q : ℤ) * r ≥ 3 * 5 := by
          nlinarith
        nlinarith
      exfalso
      norm_num [h₁₆, h₁₇, h₁₈] at h₁₄ h₁₅ hk h₀ ⊢ <;> linarith
    · -- Case k = 2
      have h₁₄ : p * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by
        ring_nf at hk ⊢
        <;> linarith
      have h₁₅ : p = 3 := by
        by_contra h₁₅
        have h₁₆ : p ≠ 3 := by tauto
        -- We need to show that p cannot be greater than 3
        have h₁₇ : p ≥ 4 := by
          by_contra h₁₇
          have h₁₈ : p ≤ 3 := by linarith
          have h₁₉ : p = 2 := by
            by_contra h₁₉
            have h₂₀ : p ≥ 3 := by omega
            have h₂₁ : p = 3 := by omega
            contradiction
          have h₂₂ : p = 2 := by omega
          have h₂₃ : q ≥ 3 := by linarith
          have h₂₄ : r ≥ 4 := by linarith
          have h₂₅ : (p : ℤ) * q ≥ 2 * 3 := by nlinarith
          have h₂₆ : (p : ℤ) * r ≥ 2 * 4 := by nlinarith
          have h₂₇ : (q : ℤ) * r ≥ 3 * 4 := by nlinarith
          have h₂₈ : (p : ℤ) * q * r ≥ 2 * 3 * 4 := by nlinarith
          have h₂₉ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
          have h₃₀ : (p : ℤ) = 2 := by omega
          have h₃₁ : (q : ℤ) ≥ 3 := by omega
          have h₃₂ : (r : ℤ) ≥ 4 := by omega
          have h₃₃ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
          have h₃₄ : (p : ℤ) = 2 := by omega
          have h₃₅ : (q : ℤ) ≥ 3 := by omega
          have h₃₆ : (r : ℤ) ≥ 4 := by omega
          have h₃₇ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
          have h₃₈ : False := by
            have h₃₉ : (p : ℤ) = 2 := by omega
            have h₄₀ : (q : ℤ) ≥ 3 := by omega
            have h₄₁ : (r : ℤ) ≥ 4 := by omega
            have h₄₂ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
            have h₄₃ : 2 * q * r - 1 = 2 * (1 * (q - 1) * (r - 1)) := by
              simp [h₃₉] at h₄₂ ⊢
              <;> ring_nf at h₄₂ ⊢ <;> linarith
            have h₄₄ : 2 * q * r - 1 = 2 * ((q - 1) * (r - 1)) := by
              ring_nf at h₄₃ ⊢ <;> linarith
            have h₄₅ : 2 * q * r - 1 = 2 * (q * r - q - r + 1) := by
              ring_nf at h₄₄ ⊢ <;> linarith
            have h₄₆ : 2 * q * r - 1 = 2 * q * r - 2 * q - 2 * r + 2 := by
              ring_nf at h₄₅ ⊢ <;> linarith
            have h₄₇ : -1 = -2 * q - 2 * r + 2 := by
              linarith
            have h₄₈ : 2 * q + 2 * r = 3 := by linarith
            have h₄₉ : (q : ℤ) ≥ 3 := by omega
            have h₅₀ : (r : ℤ) ≥ 4 := by omega
            have h₅₁ : 2 * q + 2 * r ≥ 14 := by
              nlinarith
            linarith
          exact h₃₈
        have h₁₉ : q ≥ p + 1 := by omega
        have h₂₀ : r ≥ q + 1 := by omega
        have h₂₁ : (p : ℤ) ≥ 4 := by omega
        have h₂₂ : (q : ℤ) ≥ 5 := by omega
        have h₂₃ : (r : ℤ) ≥ 6 := by omega
        have h₂₄ : (p : ℤ) * q ≥ 4 * 5 := by nlinarith
        have h₂₅ : (p : ℤ) * r ≥ 4 * 6 := by nlinarith
        have h₂₆ : (q : ℤ) * r ≥ 5 * 6 := by nlinarith
        have h₂₇ : (p : ℤ) * q * r ≥ 4 * 5 * 6 := by nlinarith
        have h₂₈ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₂₉ : (p : ℤ) ≥ 4 := by omega
        have h₃₀ : (q : ℤ) ≥ 5 := by omega
        have h₃₁ : (r : ℤ) ≥ 6 := by omega
        have h₃₂ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₃₃ : False := by
          nlinarith [sq_nonneg ((p : ℤ) - 2), sq_nonneg ((q : ℤ) - 2), sq_nonneg ((r : ℤ) - 2),
            mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
            mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₄),
            mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₄)]
        exact h₃₃
      have h₁₆ : q = 5 := by
        have h₁₇ : p = 3 := by linarith
        have h₁₈ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₁₉ : (p : ℤ) = 3 := by norm_num [h₁₇]
        have h₂₀ : (q : ℤ) ≥ 4 := by
          by_contra h₂₀
          have h₂₁ : q ≤ 3 := by linarith
          have h₂₂ : q = 3 := by linarith
          have h₂₃ : (p : ℤ) = 3 := by norm_num [h₁₇]
          have h₂₄ : (q : ℤ) = 3 := by norm_num [h₂₂]
          have h₂₅ : (r : ℤ) ≥ 4 := by linarith
          norm_num [h₁₇, h₂₂, h₂₃, h₂₄] at h₁₈
          <;>
            (try omega) <;>
            (try nlinarith) <;>
            (try
              {
                nlinarith [mul_pos (sub_pos.mpr h₀.2.1) (sub_pos.mpr h₀.2.2)]
              })
        have h₂₁ : (r : ℤ) ≥ q + 1 := by linarith
        have h₂₂ : (q : ℤ) ≥ 4 := by linarith
        have h₂₃ : (p : ℤ) = 3 := by norm_num [h₁₇]
        have h₂₄ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₂₅ : 3 * q * r - 1 = 2 * (2 * (q - 1) * (r - 1)) := by
          norm_num [h₁₇, h₁₉] at h₂₄ ⊢
          <;> ring_nf at h₂₄ ⊢ <;> linarith
        have h₂₆ : 3 * q * r - 1 = 4 * ((q - 1) * (r - 1)) := by
          ring_nf at h₂₅ ⊢
          <;> nlinarith
        have h₂₇ : 3 * q * r - 1 = 4 * (q * r - q - r + 1) := by
          ring_nf at h₂₆ ⊢
          <;> nlinarith
        have h₂₈ : 3 * q * r - 1 = 4 * q * r - 4 * q - 4 * r + 4 := by
          ring_nf at h₂₇ ⊢
          <;> nlinarith
        have h₂₉ : - q * r + 4 * q + 4 * r - 5 = 0 := by
          ring_nf at h₂₈ ⊢
          <;> nlinarith
        have h₃₀ : (q : ℤ) * r - 4 * q - 4 * r + 5 = 0 := by
          ring_nf at h₂₉ ⊢
          <;> nlinarith
        have h₃₁ : (q - 4 : ℤ) * (r - 4 : ℤ) = 11 := by
          ring_nf at h₃₀ ⊢
          <;> nlinarith
        have h₃₂ : (q : ℤ) - 4 = 1 ∧ (r : ℤ) - 4 = 11 ∨ (q : ℤ) - 4 = 11 ∧ (r : ℤ) - 4 = 1 ∨ (q : ℤ) - 4 = -1 ∧ (r : ℤ) - 4 = -11 ∨ (q : ℤ) - 4 = -11 ∧ (r : ℤ) - 4 = -1 := by
          have h₃₃ : (q : ℤ) - 4 = 1 ∨ (q : ℤ) - 4 = 11 ∨ (q : ℤ) - 4 = -1 ∨ (q : ℤ) - 4 = -11 := by
            have h₃₄ : (q : ℤ) - 4 ∣ 11 := by
              use (r : ℤ) - 4
              linarith
            have h₃₅ : (q : ℤ) - 4 = 1 ∨ (q : ℤ) - 4 = 11 ∨ (q : ℤ) - 4 = -1 ∨ (q : ℤ) - 4 = -11 := by
              have h₃₆ : (q : ℤ) - 4 = 1 ∨ (q : ℤ) - 4 = 11 ∨ (q : ℤ) - 4 = -1 ∨ (q : ℤ) - 4 = -11 := by
                rw [← Int.natAbs_dvd_natAbs] at h₃₄
                -- We use the fact that the absolute value of (q - 4) divides the absolute value of 11
                have h₃₇ : ((q : ℤ) - 4).natAbs ∣ 11 := by
                  simpa [Int.natAbs] using h₃₄
                -- Since the possible divisors of 11 are 1 and 11, we check the cases
                have h₃₈ : ((q : ℤ) - 4).natAbs = 1 ∨ ((q : ℤ) - 4).natAbs = 11 := by
                  have h₃₉ : ((q : ℤ) - 4).natAbs ∣ 11 := h₃₇
                  have h₄₀ : ((q : ℤ) - 4).natAbs ≤ 11 := Nat.le_of_dvd (by decide) h₃₉
                  interval_cases ((q : ℤ) - 4).natAbs <;> norm_num at h₃₉ ⊢ <;> omega
                cases h₃₈ with
                | inl h₃₈ =>
                  have h₄₁ : (q : ℤ) - 4 = 1 ∨ (q : ℤ) - 4 = -1 := by
                    have h₄₂ : ((q : ℤ) - 4).natAbs = 1 := h₃₈
                    have h₄₃ : (q : ℤ) - 4 = 1 ∨ (q : ℤ) - 4 = -1 := by
                      rw [Int.natAbs_eq_iff] at h₄₂
                      tauto
                    exact h₄₃
                  cases h₄₁ with
                  | inl h₄₁ =>
                    tauto
                  | inr h₄₁ =>
                    tauto
                | inr h₃₈ =>
                  have h₄₁ : (q : ℤ) - 4 = 11 ∨ (q : ℤ) - 4 = -11 := by
                    have h₄₂ : ((q : ℤ) - 4).natAbs = 11 := h₃₈
                    have h₄₃ : (q : ℤ) - 4 = 11 ∨ (q : ℤ) - 4 = -11 := by
                      rw [Int.natAbs_eq_iff] at h₄₂
                      tauto
                    exact h₄₃
                  cases h₄₁ with
                  | inl h₄₁ =>
                    tauto
                  | inr h₄₁ =>
                    tauto
              exact h₃₆
            exact h₃₅
          cases h₃₃ with
          | inl h₃₃ =>
            have h₃₄ : (q : ℤ) - 4 = 1 := h₃₃
            have h₃₅ : (r : ℤ) - 4 = 11 := by
              have h₃₆ : ((q : ℤ) - 4) * ((r : ℤ) - 4) = 11 := by
                linarith
              rw [h₃₄] at h₃₆
              linarith
            exact Or.inl ⟨h₃₄, h₃₅⟩
          | inr h₃₃ =>
            cases h₃₃ with
            | inl h₃₃ =>
              have h₃₄ : (q : ℤ) - 4 = 11 := h₃₃
              have h₃₅ : (r : ℤ) - 4 = 1 := by
                have h₃₆ : ((q : ℤ) - 4) * ((r : ℤ) - 4) = 11 := by
                  linarith
                rw [h₃₄] at h₃₆
                linarith
              exact Or.inr (Or.inl ⟨h₃₄, h₃₅⟩)
            | inr h₃₃ =>
              cases h₃₃ with
              | inl h₃₃ =>
                have h₃₄ : (q : ℤ) - 4 = -1 := h₃₃
                have h₃₅ : (r : ℤ) - 4 = -11 := by
                  have h₃₆ : ((q : ℤ) - 4) * ((r : ℤ) - 4) = 11 := by
                    linarith
                  rw [h₃₄] at h₃₆
                  linarith
                exact Or.inr (Or.inr (Or.inl ⟨h₃₄, h₃₅⟩))
              | inr h₃₃ =>
                have h₃₄ : (q : ℤ) - 4 = -11 := h₃₃
                have h₃₅ : (r : ℤ) - 4 = -1 := by
                  have h₃₆ : ((q : ℤ) - 4) * ((r : ℤ) - 4) = 11 := by
                    linarith
                  rw [h₃₄] at h₃₆
                  linarith
                exact Or.inr (Or.inr (Or.inr ⟨h₃₄, h₃₅⟩))
        rcases h₃₂ with (⟨h₃₂, h₃₃⟩ | ⟨h₃₂, h₃₃⟩ | ⟨h₃₂, h₃₃⟩ | ⟨h₃₂, h₃₃⟩)
        · -- Case 1: q - 4 = 1 and r - 4 = 11
          have h₃₄ : q = 5 := by
            linarith
          have h₃₅ : r = 15 := by
            linarith
          simp [h₃₄, h₃₅, h₁₅]
          <;> norm_num <;> omega
        · -- Case 2: q - 4 = 11 and r - 4 = 1
          have h₃₄ : q = 15 := by
            linarith
          have h₃₅ : r = 5 := by
            linarith
          have h₃₆ : r > q := by
            linarith
          linarith
        · -- Case 3: q - 4 = -1 and r - 4 = -11
          have h₃₄ : q = 3 := by
            linarith
          have h₃₅ : r = -7 := by
            linarith
          have h₃₆ : r > q := by
            linarith
          linarith
        · -- Case 4: q - 4 = -11 and r - 4 = -1
          have h₃₄ : q = -7 := by
            linarith
          have h₃₅ : r = 3 := by
            linarith
          have h₃₆ : r > q := by
            linarith
          linarith
      have h₁₇ : r = 15 := by
        have h₁₈ : p = 3 := by linarith
        have h₁₉ : q = 5 := by linarith
        have h₂₀ : (p : ℤ) * q * r - 1 = 2 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₂₁ : (p : ℤ) = 3 := by norm_num [h₁₈]
        have h₂₂ : (q : ℤ) = 5 := by norm_num [h₁₉]
        norm_num [h₁₈, h₁₉, h₂₁, h₂₂] at h₂₀
        <;> ring_nf at h₂₀ ⊢ <;> omega
      have h₁₈ : (p, q, r) = (3, 5, 15) := by
        simp_all [Prod.ext_iff]
        <;> norm_num <;> linarith
      exact Or.inr h₁₈
    · -- Case k = 3
      have h₁₄ : p * q * r - 1 = 3 * ((p - 1) * (q - 1) * (r - 1)) := by
        ring_nf at hk ⊢
        <;> linarith
      have h₁₅ : p = 2 := by
        by_contra h₁₅
        have h₁₆ : p ≥ 3 := by
          by_contra h₁₆
          have h₁₇ : p ≤ 2 := by linarith
          have h₁₈ : p = 2 := by linarith
          contradiction
        have h₁₉ : q ≥ p + 1 := by linarith
        have h₂₀ : r ≥ q + 1 := by linarith
        have h₂₁ : (p : ℤ) ≥ 3 := by linarith
        have h₂₂ : (q : ℤ) ≥ 4 := by linarith
        have h₂₃ : (r : ℤ) ≥ 5 := by linarith
        have h₂₄ : (p : ℤ) * q ≥ 3 * 4 := by nlinarith
        have h₂₅ : (p : ℤ) * r ≥ 3 * 5 := by nlinarith
        have h₂₆ : (q : ℤ) * r ≥ 4 * 5 := by nlinarith
        have h₂₇ : (p : ℤ) * q * r ≥ 3 * 4 * 5 := by nlinarith
        have h₂₈ : (p : ℤ) * q * r - 1 = 3 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₂₉ : (p : ℤ) ≥ 3 := by linarith
        have h₃₀ : (q : ℤ) ≥ 4 := by linarith
        have h₃₁ : (r : ℤ) ≥ 5 := by linarith
        have h₃₂ : (p : ℤ) * q * r - 1 = 3 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₃₃ : False := by
          nlinarith [sq_nonneg ((p : ℤ) - 2), sq_nonneg ((q : ℤ) - 2), sq_nonneg ((r : ℤ) - 2),
            mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
            mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₄),
            mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₄)]
        exact h₃₃
      have h₁₆ : q = 4 := by
        have h₁₇ : p = 2 := by linarith
        have h₁₈ : (p : ℤ) * q * r - 1 = 3 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₁₉ : (p : ℤ) = 2 := by norm_num [h₁₇]
        have h₂₀ : (q : ℤ) ≥ 3 := by
          by_contra h₂₀
          have h₂₁ : q ≤ 2 := by linarith
          have h₂₂ : q = 2 := by linarith
          have h₂₃ : (p : ℤ) = 2 := by norm_num [h₁₇]
          have h₂₄ : (q : ℤ) = 2 := by norm_num [h₂₂]
          have h₂₅ : (r : ℤ) ≥ 3 := by linarith
          norm_num [h₁₇, h₂₂, h₂₃, h₂₄] at h₁₈
          <;>
            (try omega) <;>
            (try nlinarith) <;>
            (try
              {
                nlinarith [mul_pos (sub_pos.mpr h₀.2.1) (sub_pos.mpr h₀.2.2)]
              })
        have h₂₁ : (r : ℤ) ≥ q + 1 := by linarith
        have h₂₂ : (q : ℤ) ≥ 3 := by linarith
        have h₂₃ : (p : ℤ) = 2 := by norm_num [h₁₇]
        have h₂₄ : (p : ℤ) * q * r - 1 = 3 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₂₅ : 2 * q * r - 1 = 3 * (1 * (q - 1) * (r - 1)) := by
          norm_num [h₁₇, h₁₉] at h₂₄ ⊢
          <;> ring_nf at h₂₄ ⊢ <;> linarith
        have h₂₆ : 2 * q * r - 1 = 3 * ((q - 1) * (r - 1)) := by
          ring_nf at h₂₅ ⊢
          <;> nlinarith
        have h₂₇ : 2 * q * r - 1 = 3 * (q * r - q - r + 1) := by
          ring_nf at h₂₆ ⊢
          <;> nlinarith
        have h₂₈ : 2 * q * r - 1 = 3 * q * r - 3 * q - 3 * r + 3 := by
          ring_nf at h₂₇ ⊢
          <;> nlinarith
        have h₂₉ : - q * r + 3 * q + 3 * r - 4 = 0 := by
          ring_nf at h₂₈ ⊢
          <;> nlinarith
        have h₃₀ : (q : ℤ) * r - 3 * q - 3 * r + 4 = 0 := by
          ring_nf at h₂₉ ⊢
          <;> nlinarith
        have h₃₁ : (q - 3 : ℤ) * (r - 3 : ℤ) = 5 := by
          ring_nf at h₃₀ ⊢
          <;> nlinarith
        have h₃₂ : (q : ℤ) - 3 = 1 ∧ (r : ℤ) - 3 = 5 ∨ (q : ℤ) - 3 = 5 ∧ (r : ℤ) - 3 = 1 ∨ (q : ℤ) - 3 = -1 ∧ (r : ℤ) - 3 = -5 ∨ (q : ℤ) - 3 = -5 ∧ (r : ℤ) - 3 = -1 := by
          have h₃₃ : (q : ℤ) - 3 = 1 ∨ (q : ℤ) - 3 = 5 ∨ (q : ℤ) - 3 = -1 ∨ (q : ℤ) - 3 = -5 := by
            have h₃₄ : (q : ℤ) - 3 ∣ 5 := by
              use (r : ℤ) - 3
              linarith
            have h₃₅ : (q : ℤ) - 3 = 1 ∨ (q : ℤ) - 3 = 5 ∨ (q : ℤ) - 3 = -1 ∨ (q : ℤ) - 3 = -5 := by
              have h₃₆ : (q : ℤ) - 3 = 1 ∨ (q : ℤ) - 3 = 5 ∨ (q : ℤ) - 3 = -1 ∨ (q : ℤ) - 3 = -5 := by
                rw [← Int.natAbs_dvd_natAbs] at h₃₄
                -- We use the fact that the absolute value of (q - 3) divides the absolute value of 5
                have h₃₇ : ((q : ℤ) - 3).natAbs ∣ 5 := by
                  simpa [Int.natAbs] using h₃₄
                -- Since the possible divisors of 5 are 1 and 5, we check the cases
                have h₃₈ : ((q : ℤ) - 3).natAbs = 1 ∨ ((q : ℤ) - 3).natAbs = 5 := by
                  have h₃₉ : ((q : ℤ) - 3).natAbs ∣ 5 := h₃₇
                  have h₄₀ : ((q : ℤ) - 3).natAbs ≤ 5 := Nat.le_of_dvd (by decide) h₃₉
                  interval_cases ((q : ℤ) - 3).natAbs <;> norm_num at h₃₉ ⊢ <;> omega
                cases h₃₈ with
                | inl h₃₈ =>
                  have h₄₁ : (q : ℤ) - 3 = 1 ∨ (q : ℤ) - 3 = -1 := by
                    have h₄₂ : ((q : ℤ) - 3).natAbs = 1 := h₃₈
                    have h₄₃ : (q : ℤ) - 3 = 1 ∨ (q : ℤ) - 3 = -1 := by
                      rw [Int.natAbs_eq_iff] at h₄₂
                      tauto
                    exact h₄₃
                  cases h₄₁ with
                  | inl h₄₁ =>
                    tauto
                  | inr h₄₁ =>
                    tauto
                | inr h₃₈ =>
                  have h₄₁ : (q : ℤ) - 3 = 5 ∨ (q : ℤ) - 3 = -5 := by
                    have h₄₂ : ((q : ℤ) - 3).natAbs = 5 := h₃₈
                    have h₄₃ : (q : ℤ) - 3 = 5 ∨ (q : ℤ) - 3 = -5 := by
                      rw [Int.natAbs_eq_iff] at h₄₂
                      tauto
                    exact h₄₃
                  cases h₄₁ with
                  | inl h₄₁ =>
                    tauto
                  | inr h₄₁ =>
                    tauto
              exact h₃₆
            exact h₃₅
          cases h₃₃ with
          | inl h₃₃ =>
            have h₃₄ : (q : ℤ) - 3 = 1 := h₃₃
            have h₃₅ : (r : ℤ) - 3 = 5 := by
              have h₃₆ : ((q : ℤ) - 3) * ((r : ℤ) - 3) = 5 := by
                linarith
              rw [h₃₄] at h₃₆
              linarith
            exact Or.inl ⟨h₃₄, h₃₅⟩
          | inr h₃₃ =>
            cases h₃₃ with
            | inl h₃₃ =>
              have h₃₄ : (q : ℤ) - 3 = 5 := h₃₃
              have h₃₅ : (r : ℤ) - 3 = 1 := by
                have h₃₆ : ((q : ℤ) - 3) * ((r : ℤ) - 3) = 5 := by
                  linarith
                rw [h₃₄] at h₃₆
                linarith
              exact Or.inr (Or.inl ⟨h₃₄, h₃₅⟩)
            | inr h₃₃ =>
              cases h₃₃ with
              | inl h₃₃ =>
                have h₃₄ : (q : ℤ) - 3 = -1 := h₃₃
                have h₃₅ : (r : ℤ) - 3 = -5 := by
                  have h₃₆ : ((q : ℤ) - 3) * ((r : ℤ) - 3) = 5 := by
                    linarith
                  rw [h₃₄] at h₃₆
                  linarith
                exact Or.inr (Or.inr (Or.inl ⟨h₃₄, h₃₅⟩))
              | inr h₃₃ =>
                have h₃₄ : (q : ℤ) - 3 = -5 := h₃₃
                have h₃₅ : (r : ℤ) - 3 = -1 := by
                  have h₃₆ : ((q : ℤ) - 3) * ((r : ℤ) - 3) = 5 := by
                    linarith
                  rw [h₃₄] at h₃₆
                  linarith
                exact Or.inr (Or.inr (Or.inr ⟨h₃₄, h₃₅⟩))
        rcases h₃₂ with (⟨h₃₂, h₃₃⟩ | ⟨h₃₂, h₃₃⟩ | ⟨h₃₂, h₃₃⟩ | ⟨h₃₂, h₃₃⟩)
        · -- Case 1: q - 3 = 1 and r - 3 = 5
          have h₃₄ : q = 4 := by
            linarith
          have h₃₅ : r = 8 := by
            linarith
          simp [h₃₄, h₃₅, h₁₅]
          <;> norm_num <;> omega
        · -- Case 2: q - 3 = 5 and r - 3 = 1
          have h₃₄ : q = 8 := by
            linarith
          have h₃₅ : r = 4 := by
            linarith
          have h₃₆ : r > q := by
            linarith
          linarith
        · -- Case 3: q - 3 = -1 and r - 3 = -5
          have h₃₄ : q = 2 := by
            linarith
          have h₃₅ : r = -2 := by
            linarith
          have h₃₆ : r > q := by
            linarith
          linarith
        · -- Case 4: q - 3 = -5 and r - 3 = -1
          have h₃₄ : q = -2 := by
            linarith
          have h₃₅ : r = 2 := by
            linarith
          have h₃₆ : r > q := by
            linarith
          linarith
      have h₁₇ : r = 8 := by
        have h₁₈ : p = 2 := by linarith
        have h₁₉ : q = 4 := by linarith
        have h₂₀ : (p : ℤ) * q * r - 1 = 3 * ((p - 1) * (q - 1) * (r - 1)) := by linarith
        have h₂₁ : (p : ℤ) = 2 := by norm_num [h₁₈]
        have h₂₂ : (q : ℤ) = 4 := by norm_num [h₁₉]
        norm_num [h₁₈, h₁₉, h₂₁, h₂₂] at h₂₀
        <;> ring_nf at h₂₀ ⊢ <;> omega
      have h₁₈ : (p, q, r) = (2, 4, 8) := by
        simp_all [Prod.ext_iff]
        <;> norm_num <;> linarith
      exact Or.inl h₁₈
  exact h₅