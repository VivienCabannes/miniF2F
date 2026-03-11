import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2008_p4 : (∏ k ∈ Finset.Icc (1 : ℕ) 501, ((4 : ℝ) * k + 4) / (4 * k)) = 502 := by
  norm_num [Finset.prod_range_succ]
  <;> norm_num
  <;> rw [show (4 : ℝ) = (4 : ℚ) by norm_num]
  <;> norm_cast
  <;> simp [Finset.prod_range_succ]
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all
  <;> norm_num
  <;> ring
  <;> simp_all