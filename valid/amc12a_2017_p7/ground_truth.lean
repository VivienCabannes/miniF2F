import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2017_p7 (f : ℕ → ℝ) (h₀ : f 1 = 2) (h₁ : ∀ n, 1 < n ∧ Even n → f n = f (n - 1) + 1)
  (h₂ : ∀ n, 1 < n ∧ Odd n → f n = f (n - 2) + 2) : f 2017 = 2018 := by
  have base_case : f 1 = 2 := by
    -- Simplify the goal using the given definition of f(1)
    simp_all [Nat.lt_succ_self]
    -- Use linear arithmetic to confirm the value of f(1)
    <;> linarith
  
  have inductive_step : ∀ n, n > 1 → f n = n + 1 := by
    intro n hn
    cases' n with n
    · contradiction
    cases' n with n
    · contradiction
    induction n with
    | zero =>
      simp_all [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | succ n ih =>
      cases' Nat.even_or_odd n with h h <;> simp_all [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, parity_simps]
      <;> linarith
  
  have f_2017 : f 2017 = 2017 + 1 := by
    -- Use the inductive step to directly compute f(2017)
    simpa [Nat.even_iff, Nat.odd_iff] using inductive_step 2017 (by norm_num)
  
  have result : f 2017 = 2018 := by
    -- We will show by induction that f(n) = n + 1 for all positive integers n.
    -- Base case: n = 1
    have h₃ := inductive_step 1
    have h₄ := inductive_step 2
    simp at h₃ h₄
    -- Since 1 > 1 is false, we need to adjust our base case to n = 2.
    -- Base case: n = 2
    have h₅ := h₂ 2
    have h₆ := h₁ 2
    simp at h₅ h₆
    -- Assuming f(n) = n + 1, we need to show f(n + 1) = (n + 1) + 1.
    -- For n even: f(n + 1) = f(n) + 1 = (n + 1) + 1.
    -- For n odd: f(n + 1) = f(n - 1) + 2 = (n - 1 + 1) + 2 = (n + 1) + 1.
    -- Thus, by induction, f(n) = n + 1 for all positive integers n.
    -- Special case: n = 2017, f(2017) = 2017 + 1 = 2018.
    linarith
  
  -- The result is already given as f 2017 = 2018, so we simply use it to conclude the proof.
  exact result