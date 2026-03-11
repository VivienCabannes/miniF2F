import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_765
  (x : ℤ)
  (h₀ : x < 0)
  (h₁ : (24 * x) % 1199 = 15) :
  x ≤ -449 := by
  have h_main : x ≤ -449 := by
    by_contra h
    -- Assume for contradiction that x > -449 (i.e., x ≥ -448)
    have h₂ : x ≥ -448 := by linarith
    -- Derive a contradiction using the fact that x ≡ 750 mod 1199
    have h₃ : x % 1199 = 750 := by
      -- Prove that x ≡ 750 mod 1199 using the given condition
      have h₄ : (24 * x) % 1199 = 15 := h₁
      have h₅ : (24 * x) % 1199 = (24 * x % 1199) := by simp [Int.mul_emod]
      rw [h₅] at h₄
      have h₆ : (24 : ℤ) * x % 1199 = 15 := h₄
      have h₇ : x % 1199 = 750 := by
        -- Use the fact that 24 and 1199 are coprime to solve for x mod 1199
        have h₈ : (x : ℤ) % 1199 = 750 := by
          -- Use the fact that 24 * x ≡ 15 mod 1199 implies x ≡ 750 mod 1199
          have h₉ : (24 : ℤ) * x % 1199 = 15 := h₆
          have h₁₀ : (x : ℤ) % 1199 = 750 := by
            -- Use the fact that 24 * 50 ≡ 1 mod 1199 to solve for x
            omega
          exact h₁₀
        exact h₈
      exact h₇
    -- Use the fact that x ≡ 750 mod 1199 to derive a contradiction
    have h₄ : x ≥ 750 := by
      -- Since x ≥ -448 and x ≡ 750 mod 1199, the smallest possible x is 750
      have h₅ : x % 1199 = 750 := h₃
      have h₆ : x ≥ -448 := h₂
      -- Use the fact that x ≡ 750 mod 1199 to derive a contradiction
      have h₇ : x ≥ 750 := by
        by_contra h₈
        -- If x < 750, then x ≡ 750 mod 1199 implies x ≤ -449
        have h₉ : x < 750 := by linarith
        have h₁₀ : x ≤ -449 := by
          -- Use the fact that x ≡ 750 mod 1199 to derive a contradiction
          omega
        linarith
      exact h₇
    -- Derive a contradiction using the fact that x ≥ 750 and x < 0
    linarith
  exact h_main