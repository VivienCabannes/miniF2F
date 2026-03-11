import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem amc12a_2010_p22 (x : ℝ) : 49 ≤ ∑ k ∈ (Finset.Icc (1:ℤ) (119:ℤ)), abs (k * x - 1) := by
  have hsplit : Finset.Icc (1:ℤ) 119 = Finset.Icc 1 84 ∪ Finset.Icc 85 119 := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc (1:ℤ) 84) (Finset.Icc 85 119) := by
    simp only [Finset.disjoint_left, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_union hdisj]
  set S := Finset.Icc (85:ℤ) 119
  set T := Finset.Icc (1:ℤ) 84
  -- Triangle inequality
  have hAbsS : |∑ k ∈ S, (((k:ℤ):ℝ) * x - 1)| ≤ ∑ k ∈ S, |((k:ℤ):ℝ) * x - 1| :=
    Finset.abs_sum_le_sum_abs _ _
  have hAbsT : |∑ k ∈ T, (((k:ℤ):ℝ) * x - 1)| ≤ ∑ k ∈ T, |((k:ℤ):ℝ) * x - 1| :=
    Finset.abs_sum_le_sum_abs _ _
  set A := ∑ k ∈ S, (((k:ℤ):ℝ) * x - 1)
  set B := ∑ k ∈ T, (((k:ℤ):ℝ) * x - 1)
  -- Key: A - B = 49
  suffices h49 : A - B = 49 by
    have h1 : (49 : ℝ) = |A - B| := by rw [h49]; simp
    have h2 : |A - B| ≤ |A| + |B| := abs_sub _ _
    linarith
  -- Compute A and B
  show ∑ k ∈ S, (((k:ℤ):ℝ) * x - 1) - ∑ k ∈ T, (((k:ℤ):ℝ) * x - 1) = 49
  -- Numerical values
  have hSumS : (∑ k ∈ S, (k : ℤ) : ℤ) = 3570 := by decide
  have hSumT : (∑ k ∈ T, (k : ℤ) : ℤ) = 3570 := by decide
  have hCardS : S.card = 35 := by decide
  have hCardT : T.card = 84 := by decide
  -- Expand each finset sum
  have hSval : ∑ k ∈ S, (((k:ℤ):ℝ) * x - 1) = (∑ k ∈ S, ((k:ℤ):ℝ)) * x - ↑S.card := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hTval : ∑ k ∈ T, (((k:ℤ):ℝ) * x - 1) = (∑ k ∈ T, ((k:ℤ):ℝ)) * x - ↑T.card := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Substitute numerical values
  have hSumS_real : (∑ k ∈ S, ((k:ℤ):ℝ)) = 3570 := by
    have : (∑ k ∈ S, ((k:ℤ):ℝ)) = ((∑ k ∈ S, k : ℤ) : ℝ) := by
      push_cast; rfl
    rw [this, hSumS]; norm_num
  have hSumT_real : (∑ k ∈ T, ((k:ℤ):ℝ)) = 3570 := by
    have : (∑ k ∈ T, ((k:ℤ):ℝ)) = ((∑ k ∈ T, k : ℤ) : ℝ) := by
      push_cast; rfl
    rw [this, hSumT]; norm_num
  rw [hSval, hTval, hSumS_real, hSumT_real, hCardS, hCardT]
  push_cast; ring
