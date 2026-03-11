import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12a_2020_p7
  (a : ℕ → ℕ)
  (h₀ : (a 0)^3 = 1)
  (h₁ : (a 1)^3 = 8)
  (h₂ : (a 2)^3 = 27)
  (h₃ : (a 3)^3 = 64)
  (h₄ : (a 4)^3 = 125)
  (h₅ : (a 5)^3 = 216)
  (h₆ : (a 6)^3 = 343) :
  ∑ k ∈ Finset.range 7, (6 * (a k)^2) - ↑(2 * ∑ k ∈ Finset.range 6, (a k)^2) = 658 := by
  have ha0 : a 0 = 1 := by
    have h1 : a 0 ≤ 1 := by
      by_contra h; push_neg at h
      have : (a 0) ^ 3 ≥ 8 := by nlinarith
      linarith
    interval_cases (a 0) <;> omega
  have ha1 : a 1 = 2 := by
    have h1 : a 1 ≤ 2 := by
      by_contra h; push_neg at h
      have : (a 1) ^ 3 ≥ 27 := by nlinarith
      linarith
    interval_cases (a 1) <;> omega
  have ha2 : a 2 = 3 := by
    have h1 : a 2 ≤ 3 := by
      by_contra h; push_neg at h
      have : (a 2) ^ 3 ≥ 64 := by nlinarith
      linarith
    interval_cases (a 2) <;> omega
  have ha3 : a 3 = 4 := by
    have h1 : a 3 ≤ 4 := by
      by_contra h; push_neg at h
      have : (a 3) ^ 3 ≥ 125 := by nlinarith
      linarith
    interval_cases (a 3) <;> omega
  have ha4 : a 4 = 5 := by
    have h1 : a 4 ≤ 5 := by
      by_contra h; push_neg at h
      have : (a 4) ^ 3 ≥ 216 := by nlinarith
      linarith
    interval_cases (a 4) <;> omega
  have ha5 : a 5 = 6 := by
    have h1 : a 5 ≤ 6 := by
      by_contra h; push_neg at h
      have : (a 5) ^ 3 ≥ 343 := by nlinarith
      linarith
    interval_cases (a 5) <;> omega
  have ha6 : a 6 = 7 := by
    have h1 : a 6 ≤ 7 := by
      by_contra h; push_neg at h
      have : (a 6) ^ 3 ≥ 512 := by nlinarith
      linarith
    interval_cases (a 6) <;> omega
  norm_num [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6]
