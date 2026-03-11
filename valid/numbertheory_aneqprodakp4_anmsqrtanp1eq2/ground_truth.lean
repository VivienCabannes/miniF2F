import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 400000

theorem numbertheory_aneqprodakp4_anmsqrtanp1eq2 (a : ℕ → ℝ) (h₀ : a 0 = 1)
  (h₁ : ∀ n, a (n + 1) = (∏ k ∈ Finset.range (n + 1), a k) + 4) :
  ∀ n ≥ 1, a n - Real.sqrt (a (n + 1)) = 2 := by
  -- Key: ∏ k ∈ range (n+1), a k = a(n+1) - 4
  have prod_eq : ∀ n, ∏ k ∈ Finset.range (n + 1), a k = a (n + 1) - 4 := by
    intro n; linarith [h₁ n]
  -- a 1 = 5
  have a1_val : a 1 = 5 := by
    have := h₁ 0
    simp [Finset.prod_range_succ, Finset.prod_range_zero, h₀] at this
    linarith
  -- For n ≥ 1: a(n+1) = (a(n) - 2)²
  have sq_eq : ∀ n ≥ 1, a (n + 1) = (a n - 2) ^ 2 := by
    intro n hn
    have h2 := h₁ n
    rw [Finset.prod_range_succ] at h2
    have hn' : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ := hn'
    rw [prod_eq m] at h2
    nlinarith [sq_nonneg (a (m + 1) - 2)]
  -- For n ≥ 1: a(n) ≥ 4
  have a_ge : ∀ n ≥ 1, a n ≥ 4 := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 0
      · subst hm; linarith [a1_val]
      · have hm1 : m ≥ 1 := by omega
        have := sq_eq m hm1
        have := ih hm1
        nlinarith [sq_nonneg (a m - 2)]
  -- Main proof: a(n) - √(a(n+1)) = a(n) - √((a(n)-2)²) = a(n) - (a(n)-2) = 2
  intro n hn
  rw [sq_eq n hn, Real.sqrt_sq (by linarith [a_ge n hn])]
  ring
