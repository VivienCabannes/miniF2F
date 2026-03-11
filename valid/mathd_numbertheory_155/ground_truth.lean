import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_155 :
  Finset.card (Finset.filter (fun x => x % 19 = 7) (Finset.Icc 100 999)) = 48 := by
  have h1 : ∀ (n : ℕ), n ∈ Finset.Icc 100 999 ∧ n % 19 = 7 ↔ ∃ k : ℕ, n = 19 * k + 7 ∧ 100 ≤ n ∧ n ≤ 999 := by
    intro n
    constructor
    -- Forward direction: If n is in the set of three-digit numbers divisible by 19 with a remainder of 7, then it can be expressed as 19k + 7 for some k in the range 5 to 52.
    · intro h
      rw [Finset.mem_Icc] at h
      use (n - 7) / 19
      constructor
      · omega
      · constructor
        · omega
        · omega
    -- Reverse direction: If n can be expressed as 19k + 7 for some k in the range 5 to 52, then it is a three-digit number divisible by 19 with a remainder of 7.
    · rintro ⟨k, hk1, hk2, hk3⟩
      rw [Finset.mem_Icc]
      constructor
      · omega
      · omega
  
  have h2 : ∃ k : ℕ, 19 * k + 7 ≥ 100 := by
    -- We choose k = 5 as the smallest integer satisfying the inequality.
    use 5
    -- We verify that 19 * 5 + 7 ≥ 100.
    norm_num
    -- This command simplifies the expression 19 * 5 + 7 to 102, which is indeed greater than or equal to 100.
    <;> aesop
  
  have h3 : 5 = Nat.ceil ((100 - 7) / 19 : ℚ) := by
    have h3 : ∀ (n : ℕ), n ∈ Finset.Icc 100 999 ∧ n % 19 = 7 ↔ ∃ k : ℕ, n = 19 * k + 7 ∧ 100 ≤ n ∧ n ≤ 999 := h1
    have h4 : ∃ k : ℕ, 19 * k + 7 ≥ 100 := h2
    apply Eq.symm
    norm_num
    <;> simp_all [Finset.mem_Icc, Nat.ceil_eq_iff]
    <;> norm_num
    <;> omega
  
  have h4 : ∀ k : ℕ, k ≥ 5 → 19 * k + 7 ≥ 100 := by
    intro k hk
    -- We need to show that for any k ≥ 5, 19 * k + 7 ≥ 100.
    -- This can be verified by solving the inequality 19 * k + 7 ≥ 100.
    norm_num at h3
    -- Simplify the given condition h3 to use it in the proof.
    -- h3 states that 5 is the ceiling of (100 - 7) / 19, which is approximately 5.1579.
    -- This implies that k ≥ 5 is the correct lower bound.
    omega
  
  have h5 : ∃ k : ℕ, 19 * k + 7 ≤ 999 := by
    use 52
    norm_num
  
  have h6 : 52 = Nat.floor ((999 - 7) / 19 : ℚ) := by
    apply Eq.symm
    -- We need to show that 52 equals the floor of (999 - 7) / 19.
    -- First, we compute the value of (999 - 7) / 19.
    norm_num [Nat.floor_eq_iff, Nat.ceil_eq_iff]
    -- Simplify the expression to show that the floor of (999 - 7) / 19 is indeed 52.
    <;> linarith
    -- Use linear arithmetic to verify the inequalities and equalities.
    <;> norm_num
    -- Normalize the numbers to ensure the calculations are correct.
    <;> linarith
    -- Use linear arithmetic to verify the inequalities and equalities.
    <;> norm_num
    -- Normalize the numbers to ensure the calculations are correct.
    <;> linarith
  
  have h7 : ∀ k : ℕ, k ≤ 52 → 19 * k + 7 ≤ 999 := by
    intro k hk
    -- Using the given properties and the floor function, we can directly apply the inequality.
    norm_num [Nat.floor_le, Nat.le_floor] at h6 ⊢
    <;> omega
  
  have h8 : 52 - 5 + 1 = 48 := by
    norm_num
    <;> omega
  
  have h9 : Finset.card (Finset.filter (fun x => x % 19 = 7) (Finset.Icc 100 999)) = 48 := by
    -- Simplify the expression to count the number of valid k values
    simp_all [Finset.card, Finset.filter, Finset.Icc, Nat.ceil_eq_iff, Nat.floor_eq_iff]
    -- Use Aesop to solve the remaining logical steps
    <;> aesop
  
  apply h9