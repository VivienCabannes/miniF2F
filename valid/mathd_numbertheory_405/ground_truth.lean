import Mathlib

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_405 (a b c : ℕ) (t : ℕ → ℕ) (h₀ : t 0 = 0) (h₁ : t 1 = 1)
  (h₂ : ∀ n > 1, t n = t (n - 2) + t (n - 1)) (h₃ : a ≡ 5 [MOD 16]) (h₄ : b ≡ 10 [MOD 16])
  (h₅ : c ≡ 15 [MOD 16]) : (t a + t b + t c) % 7 = 5 := by
  -- Restate recurrence in a more convenient form
  have ht : ∀ n, t (n + 2) = t n + t (n + 1) := by
    intro n; have := h₂ (n + 2) (by omega)
    simp only [show n + 2 - 2 = n from by omega, show n + 2 - 1 = n + 1 from by omega] at this
    exact this
  -- Compute t(0) through t(17) from the recurrence
  have t2 : t 2 = 1 := by rw [show (2 : ℕ) = 0 + 2 from by omega, ht, h₀, h₁]
  have t3 : t 3 = 2 := by rw [show (3 : ℕ) = 1 + 2 from by omega, ht, h₁, t2]
  have t4 : t 4 = 3 := by rw [show (4 : ℕ) = 2 + 2 from by omega, ht, t2, t3]
  have t5 : t 5 = 5 := by rw [show (5 : ℕ) = 3 + 2 from by omega, ht, t3, t4]
  have t6 : t 6 = 8 := by rw [show (6 : ℕ) = 4 + 2 from by omega, ht, t4, t5]
  have t7 : t 7 = 13 := by rw [show (7 : ℕ) = 5 + 2 from by omega, ht, t5, t6]
  have t8 : t 8 = 21 := by rw [show (8 : ℕ) = 6 + 2 from by omega, ht, t6, t7]
  have t9 : t 9 = 34 := by rw [show (9 : ℕ) = 7 + 2 from by omega, ht, t7, t8]
  have t10 : t 10 = 55 := by rw [show (10 : ℕ) = 8 + 2 from by omega, ht, t8, t9]
  have t11 : t 11 = 89 := by rw [show (11 : ℕ) = 9 + 2 from by omega, ht, t9, t10]
  have t12 : t 12 = 144 := by rw [show (12 : ℕ) = 10 + 2 from by omega, ht, t10, t11]
  have t13 : t 13 = 233 := by rw [show (13 : ℕ) = 11 + 2 from by omega, ht, t11, t12]
  have t14 : t 14 = 377 := by rw [show (14 : ℕ) = 12 + 2 from by omega, ht, t12, t13]
  have t15 : t 15 = 610 := by rw [show (15 : ℕ) = 13 + 2 from by omega, ht, t13, t14]
  have t16 : t 16 = 987 := by rw [show (16 : ℕ) = 14 + 2 from by omega, ht, t14, t15]
  have t17 : t 17 = 1597 := by rw [show (17 : ℕ) = 15 + 2 from by omega, ht, t15, t16]
  -- Prove periodicity: t(n+16) ≡ t(n) [MOD 7]
  -- Base cases: t(16) = 987, 987 % 7 = 0 = t(0) % 7
  --             t(17) = 1597, 1597 % 7 = 1 = t(1) % 7
  -- Inductive step: t(n+18) = t(n+16) + t(n+17) ≡ t(n) + t(n+1) = t(n+2) [MOD 7]
  have period : ∀ n, t (n + 16) ≡ t n [MOD 7] := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      match n with
      | 0 => show t 16 % 7 = t 0 % 7; rw [t16, h₀]
      | 1 => show t 17 % 7 = t 1 % 7; rw [t17, h₁]
      | n + 2 =>
        rw [show n + 2 + 16 = (n + 16) + 2 from by omega, ht (n + 16), ht n]
        have ih0 : t (n + 16) ≡ t n [MOD 7] := ih n (by omega)
        have ih1 : t (n + 1 + 16) ≡ t (n + 1) [MOD 7] := by
          have := ih (n + 1) (by omega)
          rwa [show n + 1 + 16 = (n + 1) + 16 from by omega]
        exact Nat.ModEq.add ih0 ih1
  -- Prove: t (16 * q + r) ≡ t r [MOD 7] by induction on q
  have reduce_aux : ∀ q r, t (16 * q + r) ≡ t r [MOD 7] := by
    intro q
    induction q with
    | zero => intro r; simp; exact Nat.ModEq.refl _
    | succ q ih =>
      intro r
      rw [show 16 * (q + 1) + r = (16 * q + r) + 16 from by ring]
      exact (period (16 * q + r)).trans (ih r)
  -- Reduce: t n ≡ t (n % 16) [MOD 7]
  have reduce : ∀ n, t n ≡ t (n % 16) [MOD 7] := by
    intro n
    conv_lhs => rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
    exact reduce_aux (n / 16) (n % 16)
  -- Use the congruence conditions: a % 16 = 5, b % 16 = 10, c % 16 = 15
  have ha : a % 16 = 5 := h₃
  have hb : b % 16 = 10 := h₄
  have hc : c % 16 = 15 := h₅
  have ra := reduce a; rw [ha] at ra
  have rb := reduce b; rw [hb] at rb
  have rc := reduce c; rw [hc] at rc
  -- Combine: t a + t b + t c ≡ t 5 + t 10 + t 15 = 5 + 55 + 610 = 670 [MOD 7]
  -- 670 % 7 = 5
  have sum_mod := (ra.add rb).add rc
  rw [t5, t10, t15] at sum_mod
  exact sum_mod
