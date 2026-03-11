import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_211 :
  Finset.card (Finset.filter (fun n => 6 ∣ 4 * ↑n - (2 : ℤ)) (Finset.range 60)) = 20 := by
  have step1 : ∀ n : ℤ, (6 ∣ 4 * n - 2) ↔ (4 * n ≡ 2 [ZMOD 6]) := by
    intro n
    constructor <;> intro h
    -- Forward direction: If 6 divides 4n - 2, then 4n is congruent to 2 modulo 6.
    -- Reverse direction: If 4n is congruent to 2 modulo 6, then 6 divides 4n - 2.
    all_goals
      simp_all [Int.ModEq, Int.emod_eq_of_lt]
    -- Simplify the expressions using properties of modular arithmetic.
    <;> omega
  
  have step2 : ∀ n : ℤ, (4 * n ≡ 2 [ZMOD 6]) ↔ (2 * n ≡ 1 [ZMOD 3]) := by
    intro n
    constructor
    -- Forward direction: If 4n ≡ 2 [ZMOD 6], then 2n ≡ 1 [ZMOD 3]
    intro h
    -- Normalize the congruence to simplify the problem
    norm_num [Int.ModEq, Int.emod_eq_of_lt] at h ⊢
    -- Use the omega tactic to solve the linear congruence
    omega
    -- Reverse direction: If 2n ≡ 1 [ZMOD 3], then 4n ≡ 2 [ZMOD 6]
    intro h
    -- Normalize the congruence to simplify the problem
    norm_num [Int.ModEq, Int.emod_eq_of_lt] at h ⊢
    -- Use the omega tactic to solve the linear congruence
    omega
  
  have step3 : ∀ n : ℤ, (2 * n ≡ 1 [ZMOD 3]) ↔ (n ≡ 2 [ZMOD 3]) := by
    intro n
    constructor
    -- Prove the forward direction: if 2n ≡ 1 [ZMOD 3], then n ≡ 2 [ZMOD 3]
    intro h
    simp only [Int.ModEq, Int.ModEq] at h ⊢
    -- Use the fact that 2n ≡ 1 [ZMOD 3] to solve for n
    omega
    -- Prove the reverse direction: if n ≡ 2 [ZMOD 3], then 2n ≡ 1 [ZMOD 3]
    intro h
    simp only [Int.ModEq, Int.ModEq] at h ⊢
    -- Use the fact that n ≡ 2 [ZMOD 3] to solve for 2n
    omega
  
  have step4 : (Finset.filter (fun n => n % 3 = 2) (Finset.range 60)).card = 20 := by
    -- Simplify the problem using modular arithmetic properties
    simp_all [Int.ModEq, Int.ModEq]
    -- Use the fact that the sequence repeats every 3 numbers
    rfl
    <;> decide
    <;> decide
    <;> decide
  
  have step5 : Finset.card (Finset.filter (fun n => 6 ∣ 4 * ↑n - (2 : ℤ)) (Finset.range 60)) = 20 := by
    -- We use the given steps to transform the original condition into a simpler one and then count the solutions.
    simpa [Int.ModEq, Int.emod_eq_of_lt] using step4
  
  exact step5