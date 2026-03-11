import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_151 : Int.ceil (Real.sqrt 27) - Int.floor (Real.sqrt 26) = 1 := by
  have sqrt27_ineq : 5 < Real.sqrt 27 ∧ Real.sqrt 27 < 6 := by
    constructor
    -- Show that 5 < sqrt(27)
    -- By the properties of square roots, if 25 < 27 < 36, then 5 < sqrt(27) < 6.
    exact by
      norm_num
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    -- Show that sqrt(27) < 6
    -- By the properties of square roots, if 25 < 27 < 36, then 5 < sqrt(27) < 6.
    exact by
      norm_num
      rw [Real.sqrt_lt (by norm_num)]
      norm_num
      linarith
  
  have sqrt26_ineq : 5 < Real.sqrt 26 ∧ Real.sqrt 26 < 6 := by
    constructor
    case left =>
      -- Use the fact that the square root of 26 is less than the square root of 27 and the given inequality to prove the lower bound.
      nlinarith [Real.sqrt_nonneg 26, Real.sqrt_nonneg 27, Real.sq_sqrt (show 0 ≤ 26 by norm_num),
        Real.sq_sqrt (show 0 ≤ 27 by norm_num), sqrt27_ineq.1]
    case right =>
      -- Use the fact that the square root of 26 is less than the square root of 27 and the given inequality to prove the upper bound.
      nlinarith [Real.sqrt_nonneg 26, Real.sqrt_nonneg 27, Real.sq_sqrt (show 0 ≤ 26 by norm_num),
        Real.sq_sqrt (show 0 ≤ 27 by norm_num), sqrt27_ineq.2]
  
  have ceil_sqrt27 : Int.ceil (Real.sqrt 27) = 6 := by
    norm_num [Int.ceil_eq_iff, sqrt27_ineq, sqrt26_ineq]
    <;> linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 27 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)]
  
  have floor_sqrt26 : Int.floor (Real.sqrt 26) = 5 := by
    -- We know the square root of 27 is between 5 and 6, and it's rounded up to 6.
    have h₀ : Int.floor (Real.sqrt 26) = 5 := by
      -- We use the fact that the square root of 26 is less than the square root of 27, which is between 5 and 6.
      have h₁ := sqrt27_ineq.2
      have h₂ := sqrt26_ineq.2
      have h₃ := sqrt26_ineq.1
      -- By linear arithmetic, we can conclude that the floor of the square root of 26 is 5.
      norm_num [Int.floor_eq_iff, Real.sqrt_le_sqrt] at h₁ h₂ h₃ ⊢
      constructor <;> nlinarith [Real.sq_sqrt (show 0 ≤ 26 by norm_num), Real.sq_sqrt (show 0 ≤ 27 by norm_num)]
    -- We have already determined that the floor of the square root of 26 is 5.
    exact h₀
  
  have final_calc : Int.ceil (Real.sqrt 27) - Int.floor (Real.sqrt 26) = 1 := by
    norm_num [ceil_sqrt27, floor_sqrt26]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
    <;> norm_num [sqrt27_ineq, sqrt26_ineq]
    <;> linarith [sqrt27_ineq, sqrt26_ineq]
  
  -- This theorem is trivially true by the given assumptions and the properties of the ceiling and floor functions.
  assumption