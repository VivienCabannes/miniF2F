import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 3200000

-- Key polynomial lemma: 4*(p²+q²+pq)³ ≥ 27*p²*q²*(p+q)²
-- Proof: the difference factors as (p-q)²*(p+2q)²*(2p+q)²
private lemma poly_ineq1 (p q : ℝ) :
    27 * p ^ 2 * q ^ 2 * (p + q) ^ 2 ≤ 4 * (p ^ 2 + q ^ 2 + p * q) ^ 3 := by
  nlinarith [sq_nonneg ((p - q) * (p + 2 * q) * (2 * p + q)),
             sq_nonneg (p * q),
             sq_nonneg ((p - q) * (p + 2 * q)),
             sq_nonneg ((p - q) * (2 * p + q)),
             sq_nonneg ((p + 2 * q) * (2 * p + q)),
             sq_nonneg (p - q), sq_nonneg (p + 2 * q), sq_nonneg (2 * p + q)]

-- AM-GM for 4 terms specialized: 256*u³*v ≤ (3u+v)⁴ for u,v ≥ 0
-- Proof: (3u+v)⁴ - 256*u³*v = (u-v)²*(81u²+14uv+v²) ≥ 0
private lemma poly_ineq2 (u v : ℝ) (_ : 0 ≤ u) (_ : 0 ≤ v) :
    256 * u ^ 3 * v ≤ (3 * u + v) ^ 4 := by
  nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v,
             sq_nonneg (u * v),
             sq_nonneg ((u - v) * (9 * u + v)),
             sq_nonneg (u * (u - v)),
             sq_nonneg (3 * u ^ 2 - v ^ 2)]

-- Main polynomial inequality: 512 * LHS² ≤ 81 * S⁴
private lemma poly_main (a b c : ℝ) :
    512 * (a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)) ^ 2
    ≤ 81 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 4 := by
  set p := a - b
  set q := b - c
  set s := a + b + c
  have hident : a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)
      = p * q * (p + q) * s := by ring
  have hS : 3 * (a ^ 2 + b ^ 2 + c ^ 2) = 2 * p ^ 2 + 2 * q ^ 2 + 2 * p * q + s ^ 2 := by ring
  rw [hident]
  suffices h : 512 * p ^ 2 * q ^ 2 * (p + q) ^ 2 * s ^ 2
      ≤ (2 * p ^ 2 + 2 * q ^ 2 + 2 * p * q + s ^ 2) ^ 4 by
    nlinarith [hS]
  have h1 := poly_ineq1 p q
  have hT_half : 0 ≤ p ^ 2 + q ^ 2 + p * q := by nlinarith [sq_nonneg (2 * p + q), sq_nonneg q]
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have h2 : 2048 * (p ^ 2 + q ^ 2 + p * q) ^ 3 * s ^ 2
      ≤ 27 * (2 * (p ^ 2 + q ^ 2 + p * q) + s ^ 2) ^ 4 := by
    have := poly_ineq2 (2 * (p ^ 2 + q ^ 2 + p * q) / 3) (s ^ 2)
        (by linarith) hs2
    nlinarith
  have hTeq : 2 * (p ^ 2 + q ^ 2 + p * q) + s ^ 2 =
      2 * p ^ 2 + 2 * q ^ 2 + 2 * p * q + s ^ 2 := by ring
  rw [hTeq] at h2
  nlinarith [sq_nonneg (p * q * (p + q) * s),
             mul_nonneg hT_half hs2,
             sq_nonneg (p ^ 2 + q ^ 2 + p * q)]

theorem imo_2006_p3 (a b c : ℝ) :
  a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2) ≤
  9 * Real.sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  by_cases h : a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2) ≤ 0
  · calc a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)
        ≤ 0 := h
      _ ≤ 9 * Real.sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
          apply mul_nonneg
          · apply div_nonneg
            · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 9) (Real.sqrt_nonneg _)
            · norm_num
          · positivity
  · push_neg at h
    -- LHS > 0. Need to show LHS ≤ RHS.
    -- Strategy: show LHS² ≤ RHS², then use that both are positive.
    set L := a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)
    set S := a ^ 2 + b ^ 2 + c ^ 2
    -- S > 0 (since L > 0 implies a,b,c not all zero)
    have hS_pos : 0 < S := by
      by_contra hS_neg
      push_neg at hS_neg
      have hS_nn : 0 ≤ S := by positivity
      have hS0 : S = 0 := le_antisymm hS_neg hS_nn
      have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
      have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
      have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
      have : L = 0 := by simp only [L]; rw [ha, hb, hc]; ring
      linarith
    -- Main polynomial inequality
    have hpoly := poly_main a b c
    -- hpoly : 512 * L ^ 2 ≤ 81 * S ^ 4
    -- We need: L ≤ 9 * sqrt 2 / 32 * S ^ 2
    -- Since L > 0 and the RHS involves sqrt, we use:
    -- L ≤ R ↔ L² ≤ R² (when both positive)
    -- R² = (9 * sqrt 2 / 32)² * S⁴ = 81 * 2 / 1024 * S⁴ = 81/512 * S⁴
    -- So L² ≤ 81/512 * S⁴ ↔ 512 * L² ≤ 81 * S⁴ (which is hpoly)
    have hR_pos : 0 < 9 * Real.sqrt 2 / 32 := by
      apply _root_.div_pos
      · exact mul_pos (by norm_num : (0:ℝ) < 9) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))
      · norm_num
    -- It suffices to show L^2 ≤ (9*sqrt 2/32 * S^2)^2
    suffices hsq : L ^ 2 ≤ (9 * Real.sqrt 2 / 32 * S ^ 2) ^ 2 by
      have hRS_nonneg : 0 ≤ 9 * Real.sqrt 2 / 32 * S ^ 2 := le_of_lt (mul_pos hR_pos (pow_pos hS_pos 2))
      exact le_of_sq_le_sq hsq hRS_nonneg
    -- Compute (9*sqrt 2/32 * S^2)^2 = (9*sqrt 2/32)^2 * S^4
    have hRHS_sq : (9 * Real.sqrt 2 / 32 * S ^ 2) ^ 2 = (81 / 512 : ℝ) * S ^ 4 := by
      rw [mul_pow, div_pow, mul_pow, sq (Real.sqrt 2),
          Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    rw [hRHS_sq]
    -- Need: L^2 ≤ 81/512 * S^4, i.e., 512*L^2 ≤ 81*S^4
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 512)]
    -- Now goal should be L^2 * 512 ≤ 81 * S^4
    linarith
