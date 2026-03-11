import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 800000

theorem mathd_numbertheory_530 (n k : ℕ) (h₀ : 0 < n ∧ 0 < k) (h₀ : (n : ℝ) / k < 6)
  (h₁ : (5 : ℝ) < n / k) : 22 ≤ Nat.lcm n k / Nat.gcd n k := by
  -- Derive k > 0 from h₁
  have hk_pos : (0 : ℝ) < k := by
    by_contra h
    push_neg at h
    have hk0 : (k : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg k)
    rw [hk0, div_zero] at h₁
    exact absurd h₁ (by norm_num)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hn_pos : (0 : ℝ) < n := by
    have := (div_pos_iff_of_pos_right hk_pos).mp (lt_trans (by norm_num : (0:ℝ) < 5) h₁)
    exact this
  -- Key inequalities: 5 * k < n and n < 6 * k (as reals)
  have h5k_lt_n_real : (5 : ℝ) * k < n := by
    rw [lt_div_iff₀ hk_pos] at h₁
    linarith
  have hn_lt_6k_real : (n : ℝ) < 6 * k := by
    have := h₀
    rwa [div_lt_iff₀ hk_pos] at this
  -- Now work with natural numbers
  have hk_pos_nat : 0 < k := by exact_mod_cast hk_pos
  have hn_pos_nat : 0 < n := by exact_mod_cast hn_pos
  -- Cast to natural number inequalities
  have h5k_lt_n_nat : 5 * k < n := by exact_mod_cast h5k_lt_n_real
  have hn_lt_6k_nat : n < 6 * k := by exact_mod_cast hn_lt_6k_real
  -- Let g = gcd n k
  set g := Nat.gcd n k with hg_def
  have hg_pos : 0 < g := by positivity
  have hg_dvd_n : g ∣ n := Nat.gcd_dvd_left n k
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_right n k
  set n' := n / g with hn'_def
  set k' := k / g with hk'_def
  have hn_eq : n = n' * g := (Nat.div_mul_cancel hg_dvd_n).symm
  have hk_eq : k = k' * g := (Nat.div_mul_cancel hg_dvd_k).symm
  -- Key: gcd(n, k) = g, so after substitution, gcd(n'*g, k'*g) = g * gcd(n', k') = g
  -- since gcd(n', k') = 1 (by definition of reducing by gcd)
  -- lcm n k = n * k / gcd n k
  -- We prove lcm n k / gcd n k = n' * k' directly
  have hgcd_eq : Nat.gcd n k = g := rfl
  have hlcm : Nat.lcm n k / g = n' * k' := by
    have hg_ne : g ≠ 0 := Nat.ne_zero_of_lt (Nat.zero_lt_of_lt hg_pos)
    rw [Nat.lcm, hgcd_eq]
    -- lcm n k = n * k / g, so lcm n k / g = n * k / g / g
    -- But n = n' * g, k = k' * g
    -- n * k / g = n' * g * (k' * g) / g = n' * k' * g
    -- Then n' * k' * g / g = n' * k'
    rw [hn_eq, hk_eq]
    rw [show n' * g * (k' * g) / g = n' * k' * g from by
      rw [show n' * g * (k' * g) = n' * k' * g * g from by ring]
      exact Nat.mul_div_cancel _ hg_pos]
    exact Nat.mul_div_cancel _ hg_pos
  -- From the inequalities: 5 * k' < n' and n' < 6 * k'
  have hk'_pos : 0 < k' := by
    exact Nat.div_pos (Nat.le_of_dvd hk_pos_nat hg_dvd_k) hg_pos
  have hn'_pos : 0 < n' := by
    exact Nat.div_pos (Nat.le_of_dvd hn_pos_nat hg_dvd_n) hg_pos
  have h5k'_lt_n' : 5 * k' < n' := by
    have h1 : 5 * k' * g < n' * g := by
      calc 5 * k' * g = 5 * (k' * g) := by ring
        _ < n' * g := by rw [← hn_eq, ← hk_eq]; linarith
    exact lt_of_mul_lt_mul_of_nonneg_right h1 (Nat.zero_le g)
  have hn'_lt_6k' : n' < 6 * k' := by
    have h1 : n' * g < 6 * k' * g := by
      calc n' * g < 6 * (k' * g) := by rw [← hn_eq, ← hk_eq]; linarith
        _ = 6 * k' * g := by ring
    exact lt_of_mul_lt_mul_of_nonneg_right h1 (Nat.zero_le g)
  -- Now we need to show 22 ≤ n' * k'
  suffices 22 ≤ n' * k' by rwa [hlcm]
  by_cases hk'3 : k' ≥ 3
  · have hn'_ge : n' ≥ 5 * k' + 1 := by omega
    calc n' * k' ≥ (5 * k' + 1) * k' := by nlinarith
      _ ≥ (5 * 3 + 1) * 3 := by nlinarith
      _ = 48 := by norm_num
      _ ≥ 22 := by norm_num
  · have : k' ≤ 2 := by omega
    interval_cases k' <;> omega
