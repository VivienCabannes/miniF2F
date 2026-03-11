import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  obtain ⟨hx, hy, hz⟩ := h₀
  have hxy : (0 : ℝ) < x + y := by linarith
  have hyz : (0 : ℝ) < y + z := by linarith
  have hzx : (0 : ℝ) < z + x := by linarith
  have hxyz : (0 : ℝ) < x + y + z := by linarith
  suffices h : 0 ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) - 9 / (x + y + z) by linarith
  have h1 : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) - 9 / (x + y + z) =
    ((x - y) ^ 2 * (x + y) + (y - z) ^ 2 * (y + z) + (z - x) ^ 2 * (z + x)) /
    ((x + y + z) * ((x + y) * ((y + z) * (z + x)))) := by
    field_simp [hxy.ne', hyz.ne', hzx.ne', hxyz.ne']
    ring
  rw [h1]
  apply div_nonneg
  · have h2 : 0 ≤ (x - y) ^ 2 * (x + y) := mul_nonneg (sq_nonneg _) hxy.le
    have h3 : 0 ≤ (y - z) ^ 2 * (y + z) := mul_nonneg (sq_nonneg _) hyz.le
    have h4 : 0 ≤ (z - x) ^ 2 * (z + x) := mul_nonneg (sq_nonneg _) hzx.le
    linarith
  · positivity
