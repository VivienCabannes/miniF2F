import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 6400000

-- ha15: (1 + -(1/s)) / (1 - 1*-(1/s)) = 2 - s
-- denom = 1 + 1/s. field_simp needs s ≠ 0.
-- After clearing /s: s + 1. Need s + 1 ≠ 0.
-- But how does field_simp see the whole denominator? Let me check.
-- From error: the denom in normalized form would be (s+1)/s or s + 1
-- Actually let me just try providing just hs_ne and s+1≠0
example (s : ℝ) (hs_ne : s ≠ 0) (hss : s * s = 3) (hs_gt1 : s > 1) :
  (1 + -(1 / s)) / (1 - 1 * -(1 / s)) = 2 - s := by
  have h2 : (s : ℝ) + 1 ≠ 0 := by linarith
  field_simp [hs_ne, h2]; nlinarith [hss]

-- ha16 inner: 1 - -(1/s) * (2-s) = 2/s
-- This is: 1 + (2-s)/s = (s + 2 - s)/s = 2/s
-- field_simp should clear this if we give hs_ne
example (s : ℝ) (hs_ne : s ≠ 0) (hss : s * s = 3) (hs_gt1 : s > 1) :
  1 - -(1 / s) * (2 - s) = 2 / s := by
  field_simp [hs_ne]; nlinarith [hss]

-- ha16 outer: (-(1/s) + (2-s)) / (2/s) = s - 2
-- After providing hd (the denominator = 2/s ≠ 0), field_simp should clear
-- But the denominator in the actual proof is not 2/s, it's 1 - -(1/s) * (2-s)
-- which field_simp normalizes to something. Let me check:
-- field_simp sees: 1 - -(1/s) * (2-s) after clearing /s becomes s + (2-s) = 2
-- So the normalized denom is 2 (after clearing /s factor)
-- Actually, field_simp with hs_ne should clear /s and leave:
-- (-(1) + s*(2-s)) / (s + (2-s)) = s - 2  which is (-1 + 2s - s²) / 2 = s - 2
-- i.e., (2s - s² - 1) / 2 = s - 2, i.e., 2s - 3 - 1 = 2(s-2) = 2s - 4
-- 2s - 4 = 2s - 4. True!
-- But the denominator in the goal was hd (provided separately)
-- In the actual code, hd is proved separately and passed to field_simp

-- Let me test the actual form: after rw with ha14 and ha15
-- a14 = -(1/s), a15 = 2 - s
-- goal after rw: (-(1/s) + (2-s)) / (1 - (-(1/s))*(2-s)) = s - 2
example (s : ℝ) (hs_ne : s ≠ 0) (hss : s * s = 3) (hs_gt1 : s > 1) :
  (-(1 / s) + (2 - s)) / (1 - -(1 / s) * (2 - s)) = s - 2 := by
  have hd : s - -(2 - s) ≠ 0 := by linarith
  field_simp [hs_ne, hd]; nlinarith [hss]

-- ha20: ((s-2) + (s-2)) / (1 - (s-2)*(s-2)) = -(1/s)
-- denom = 1 - (s-2)² = 1 - (s²-4s+4) = 1-3+4s-4 = 4s-6 = 2(2s-3) ≠ 0
-- field_simp normalizes: 1 - (s-2)^2 or 1 - (s-2)*(s-2)
example (s : ℝ) (hs_ne : s ≠ 0) (hss : s * s = 3) (hs_gt1 : s > 1) :
  ((s - 2) + (s - 2)) / (1 - (s - 2) * (s - 2)) = -(1 / s) := by
  have hd : 1 - (s - 2) ^ 2 ≠ 0 := by nlinarith [hss]
  field_simp [hs_ne, hd]; nlinarith [hss]

-- ha21: ((s-2) + (-(1/s))) / (1 - (s-2)*(-(1/s))) = -1
-- denom = 1 + (s-2)/s = (s + s - 2)/s = (2s-2)/s = 2(s-1)/s
-- field_simp normalized form: s - -(s-2) = s + s - 2 = 2s-2 = 2(s-1)
-- Need: s - -(s-2) ≠ 0 or 2s - 2 ≠ 0 or s - 1 ≠ 0
example (s : ℝ) (hs_ne : s ≠ 0) (hss : s * s = 3) (hs_gt1 : s > 1) :
  ((s - 2) + -(1 / s)) / (1 - (s - 2) * -(1 / s)) = -1 := by
  have hd : s - -(s - 2) ≠ 0 := by nlinarith
  field_simp [hs_ne, hd]; nlinarith [hss]

-- ha22: (-(1/s) + (-1)) / (1 - (-(1/s))*(-1)) = -((s+1)/(s-1))
-- denom = 1 - 1/s = (s-1)/s
-- field_simp needs s - 1 ≠ 0 and s ≠ 0
example (s : ℝ) (hs_ne : s ≠ 0) (hss : s * s = 3) (hs_gt1 : s > 1) :
  (-(1 / s) + -1) / (1 - -(1 / s) * -1) = -((s + 1) / (s - 1)) := by
  have h1 : s - 1 ≠ 0 := by linarith
  field_simp [hs_ne, h1]; nlinarith [hss]

-- ha23: (-1 + (-(s+1)/(s-1))) / (1 - (-1)*(-(s+1)/(s-1))) = s
-- denom = 1 - (s+1)/(s-1) = ((s-1)-(s+1))/(s-1) = -2/(s-1)
-- field_simp normalized: (s-1) - (s+1) = -2, so need -2 ≠ 0 or s-1-(s+1) ≠ 0
-- Actually field_simp sees: 1 - -1 * -(s+1)/(s-1) = 1 - (s+1)/(s-1)
-- After clearing /(s-1): (s-1) - (s+1) ≠ 0
example (s : ℝ) (hs_ne : s ≠ 0) (hss : s * s = 3) (hs_gt1 : s > 1) :
  (-1 + -((s + 1) / (s - 1))) / (1 - -1 * -((s + 1) / (s - 1))) = s := by
  have h1 : s - 1 ≠ 0 := by linarith
  have hd : (s - 1) - (s + 1) ≠ 0 := by linarith
  field_simp [hs_ne, h1, hd]; nlinarith [hss]
