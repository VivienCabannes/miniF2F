import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_530 (n k : ℕ) (h₀ : 0 < n ∧ 0 < k) (h₀ : (n : ℝ) / k < 6)
  (h₁ : (5 : ℝ) < n / k) : 22 ≤ Nat.lcm n k / Nat.gcd n k := by
  have h₃ : ∃ d a b, d = Nat.gcd n k ∧ n = d * a ∧ k = d * b ∧ Nat.gcd a b = 1 := by
    use Nat.gcd n k
    use n / Nat.gcd n k
    use k / Nat.gcd n k
    have h₂ : 0 < n := by linarith
    have h₃ : 0 < k := by linarith
    have h₄ : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left k h₂
    have h₅ : n = Nat.gcd n k * (n / Nat.gcd n k) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n k)]
    have h₆ : k = Nat.gcd n k * (k / Nat.gcd n k) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right n k)]
    have h₇ : Nat.gcd (n / Nat.gcd n k) (k / Nat.gcd n k) = 1 := by
      rw [Nat.gcd_div (Nat.gcd_dvd_left n k) (Nat.gcd_dvd_right n k)]
      <;> simp [h₄]
    exact ⟨rfl, h₅, h₆, h₇⟩
  have h₄ : ∀ d a b, d = Nat.gcd n k → n = d * a → k = d * b → 5 * b < a ∧ a < 6 * b := by
    intro d a b h₄ h₅ h₆
    have h₇ : 0 < d := by
      -- Since d is the gcd of n and k, and both n and k are positive, d must be positive.
      have h₇ : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left k (by linarith)
      linarith
    have h₈ : 0 < a := by
      -- Since n = d * a, and d is positive, a must be positive.
      have h₈ : 0 < n := by linarith
      have h₉ : 0 < d := by linarith
      nlinarith
    have h₉ : 0 < b := by
      -- Since k = d * b, and d is positive, b must be positive.
      have h₉ : 0 < k := by linarith
      have h₁₀ : 0 < d := by linarith
      nlinarith
    constructor
    -- We need to show that 5 * b < a.
    -- From the given inequalities, we can derive this.
    field_simp [h₅, h₆] at h₀ h₁ ⊢
    rw [div_lt_iff] at h₀ <;> rw [lt_div_iff] at h₁ <;> norm_cast at h₀ h₁ ⊢ <;> nlinarith
    -- We need to show that a < 6 * b.
    -- From the given inequalities, we can derive this.
    field_simp [h₅, h₆] at h₀ h₁ ⊢
    rw [div_lt_iff] at h₀ <;> rw [lt_div_iff] at h₁ <;> norm_cast at h₀ h₁ ⊢ <;> nlinarith
  have h₅ : ∀ a b, 5 * b < a → a < 6 * b → Nat.gcd a b = 1 → 22 ≤ a * b := by
    have h₅ : ∀ a b : ℕ, 5 * b < a → a < 6 * b → Nat.gcd a b = 1 → 22 ≤ a * b := by
      intro a b h₅ h₆ h₇
      have h₈ : a * b ≥ 22 := by
        by_contra h₈
        have h₉ : a * b ≤ 21 := by
          linarith
        have h₁₀ : a ≤ 21 := by
          nlinarith
        have h₁₁ : b ≤ 21 := by
          nlinarith
        interval_cases a <;> interval_cases b <;> contradiction
      linarith
    exact h₅
  have h₆ : 22 ≤ Nat.lcm n k / Nat.gcd n k := by
    obtain ⟨d, a, b, hd, ha, hb, hgcd⟩ := h₃
    have h₆ := h₄ d a b hd ha hb
    have h₇ := h₅ a b
    have h₈ : 0 < d := by
      nlinarith
    have h₉ : 0 < a := by
      nlinarith
    have h₁₀ : 0 < b := by
      nlinarith
    have h₁₁ : Nat.gcd n k = d := by
      nlinarith
    have h₁₂ : Nat.lcm n k = d * a * b := by
      nlinarith [Nat.gcd_mul_lcm n k, Nat.mul_comm a b, Nat.mul_comm d a, Nat.mul_comm d b]
    have h₁₃ : d * a * b / d = a * b := by
      rw [Nat.mul_comm]
      exact by
        rw [Nat.div_eq_of_eq_mul_left] <;> nlinarith
    rw [h₁₁, h₁₂, h₁₃]
    nlinarith [h₆, h₇]
  exact h₆