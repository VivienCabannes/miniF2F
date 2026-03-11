import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 800000

theorem imo_1982_p1
  (f : ℕ → ℕ)
  (h₀ : ∀ m n, (0 < m ∧ 0 < n) → f (m + n) - f m - f n = 0 ∨ f (m + n) - f m - f n = 1)
  (h₁ : f 2 = 0)
  (h₂ : 0 < f 3)
  (h₃ : f 9999 = 3333) :
  f 1982 = 660 := by
  -- From h₀: f(m+n) ≤ f(m) + f(n) + 1
  have hsub : ∀ m n, 0 < m → 0 < n → f (m + n) ≤ f m + f n + 1 := by
    intro m n hm hn; have h := h₀ m n ⟨hm, hn⟩; omega
  have hf1 : f 1 = 0 := by have := hsub 1 1 (by omega) (by omega); omega
  have hf3 : f 3 = 1 := by have := hsub 1 2 (by omega) (by omega); omega
  -- f(n+1) ≤ f(n) + 1
  have hstep1 : ∀ n, 0 < n → f (n + 1) ≤ f n + 1 := by
    intro n hn; have := hsub n 1 hn (by omega); omega
  -- f(n+2) ≤ f(n) + 1
  have hstep2 : ∀ n, 0 < n → f (n + 2) ≤ f n + 1 := by
    intro n hn; have := hsub n 2 hn (by omega); omega
  -- f(n+3) ≤ f(n) + 2
  have hstep3 : ∀ n, 0 < n → f (n + 3) ≤ f n + 2 := by
    intro n hn; have := hsub n 3 hn (by omega); omega
  -- Lower bound from stepping backwards: f(n) ≥ f(n+1) - 1
  -- Upper bound: f(n+2) ≤ f(n) + 1 → f(n) ≥ f(n+2) - 1
  -- f(n) ≥ f(n+3) - 2
  -- Key: f(2n) ≤ 2*f(n) + 1
  have hdouble : ∀ n, 0 < n → f (2 * n) ≤ 2 * f n + 1 := by
    intro n hn; have := hsub n n hn hn; omega
  -- f(3n) ≤ 3*f(n) + 2
  have htriple : ∀ n, 0 < n → f (3 * n) ≤ 3 * f n + 2 := by
    intro n hn
    have h1 := hsub n (2 * n) hn (by omega)
    have h2 := hdouble n hn
    omega
  -- Lower bounds from f(9999):
  -- f(a) + f(b) + 1 ≥ f(a+b) for positive a,b. With a+b = 9999:
  -- f(a) ≥ f(9999) - f(b) - 1 = 3332 - f(b)
  -- f(a) ≥ f(9999) - 1 - f(9999-a) = 3332 - f(9999-a)
  have hlower : ∀ a, 0 < a → a < 9999 → f a ≥ 3332 - f (9999 - a) := by
    intro a ha ha2
    have h := hsub a (9999 - a) ha (by omega)
    have : a + (9999 - a) = 9999 := by omega
    rw [this] at h; omega
  -- Iterated tripling bounds:
  -- f(3333) ≥ (f(9999) - 2) / 3 = 1110 (from f(9999) ≤ 3*f(3333) + 2)
  have hf3333_lb : f 3333 ≥ 1111 := by
    have := htriple 3333 (by omega); omega
  -- f(3333) ≤ f(3331) + 2 ≤ ... ≤ f(1) + 2*1111 = 2222 (too loose)
  -- Better: use f(9999) = f(3333 + 6666) ≤ f(3333) + f(6666) + 1
  --         and f(6666) = f(2*3333) ≤ 2*f(3333) + 1
  --         so 3333 ≤ f(3333) + 2*f(3333) + 2 = 3*f(3333) + 2
  --         → f(3333) ≥ 1111 (already have)
  -- Upper bound: f(3333) ≤ ?
  -- f(6666) ≥ 3332 - f(3333) (from hlower with a=6666)
  -- f(6666) ≤ 2*f(3333) + 1
  -- So 3332 - f(3333) ≤ 2*f(3333) + 1 → f(3333) ≥ 1110 (weaker)
  -- f(3333) ≤ f(3333). Trivial.
  -- Use f(9999) = f(3*3333), f(3*3333) ≤ 3*f(3333) + 2
  -- 3333 ≤ 3*f(3333) + 2 → f(3333) ≥ 1111
  -- Also f(3333) ≤ ? Need upper bound.
  -- f(3333) = f(3*1111) ≤ 3*f(1111) + 2
  -- f(1111) = f(3*370 + 1). f(1111) ≤ f(1110) + 1 = f(3*370) + 1 ≤ 3*f(370) + 3

  -- Actually let's try an entirely different, direct approach.
  -- Compute tight bounds on f(1982) by combining upper and lower bounds.

  -- f(1982) ≤ f(1980) + 1  (step2)
  -- f(1980) = f(2*990) ≤ 2*f(990) + 1
  -- f(990) = f(3*330) ≤ 3*f(330) + 2
  -- f(330) = f(3*110) ≤ 3*f(110) + 2
  -- f(110) = f(2*55) ≤ 2*f(55) + 1
  -- f(55) = f(3*18 + 1) ≤ f(54) + 1 = f(3*18) + 1 ≤ 3*f(18) + 3
  -- f(18) = f(3*6) ≤ 3*f(6) + 2
  -- f(6) = f(3+3) ≤ f(3) + f(3) + 1 = 3
  -- f(18) ≤ 3*3 + 2 = 11
  -- f(55) ≤ 3*11 + 3 = 36
  -- f(110) ≤ 2*36 + 1 = 73
  -- f(330) ≤ 3*73 + 2 = 221
  -- f(990) ≤ 3*221 + 2 = 665
  -- f(1980) ≤ 2*665 + 1 = 1331
  -- f(1982) ≤ 1331 + 1 = 1332. Still too loose (should be 660).

  -- These upper bounds aren't tight because we're going "up" via tripling.
  -- The tight bound should come from f(n) ≤ n/2 via step2.
  -- f(1982) ≤ f(2) + 990 = 990.

  -- Lower bound:
  -- f(1982) ≥ 3332 - f(8017). f(8017) ≤ 8017/2 = 4008. f(1982) ≥ 3332 - 4008 < 0. Useless.

  -- Better lower bound using tripling:
  -- f(5946) = f(3*1982) ≤ 3*f(1982) + 2
  -- f(5946) ≥ 3332 - f(4053). f(4053) ≤ 4053/2 = 2026.
  -- f(5946) ≥ 3332 - 2026 = 1306
  -- So 1306 ≤ 3*f(1982) + 2 → f(1982) ≥ 435.

  -- Iterate: f(4053) ≥ 3332 - f(5946).
  -- f(5946) ≤ 5946/2 = 2973. f(4053) ≥ 3332 - 2973 = 359.
  -- So f(5946) ≥ 3332 - 359 = 2973. Hmm, same bound.

  -- Try: f(5946) = f(2*2973) ≤ 2*f(2973) + 1 → f(2973) ≥ (1306-1)/2 = 652.5 → f(2973) ≥ 653.
  -- f(2973) = f(3*991) ≤ 3*f(991) + 2 → f(991) ≥ (653-2)/3 = 217.
  -- f(991) = f(1982/2 roughly). Actually 991 ≠ 1982/2.
  -- f(991) = f(1982 - 991). f(1982) ≥ 3332 - f(8017)... no wait.
  -- f(1982) = f(991 + 991) ≤ 2*f(991) + 1. And f(1982) ≥ 435 → doesn't help.

  -- This is incredibly tedious. Let me try using `nlinarith` with many hypotheses.
  -- Or maybe just use a very long chain of bounds.

  -- I'll try a different decomposition strategy.
  -- Key: f(n) ≈ n/3 = 660.67 for n = 1982.
  -- Upper bound chain: f(1982) ≤ f(1980) + 1 ≤ f(1978) + 2 ≤ ... ≤ f(2) + 990 = 990
  -- So f(1982) ≤ 990.

  -- Lower bound: need to show f(1982) ≥ 660.
  -- Strategy: f(5946) = f(3*1982). Use f(9999) = f(5946 + 4053).
  -- f(9999) ≤ f(5946) + f(4053) + 1.
  -- f(4053) ≤ 4053/2 = 2026 (from step2 chain).
  -- Actually: f(4053) ≤ f(4051) + 1 ≤ ... ≤ f(3) + (4053-3)/2 = 1 + 2025 = 2026.
  -- So f(5946) ≥ 3333 - 2026 - 1 = 1306.
  -- f(5946) = f(3*1982) ≤ 3*f(1982) + 2.
  -- 3*f(1982) + 2 ≥ 1306 → f(1982) ≥ 435. (Not tight enough.)

  -- Need tighter bound on f(4053).
  -- f(4053) is approximately 4053/3 = 1351. Let's bound it.
  -- f(4053) = f(3*1351). f(12159) = f(3*4053). But 12159 > 9999, can't use h₃ directly.
  -- f(4053) ≥ 3332 - f(5946) ≥ 3332 - 5946/2 = 3332 - 2973 = 359.
  -- So f(4053) ∈ [359, 2026].

  -- Iterate to get tighter bounds:
  -- Round 2: f(5946) ≥ 3333 - 1 - f(4053). f(4053) ≤ 2026 → f(5946) ≥ 1306.
  --          f(4053) ≥ 3333 - 1 - f(5946). f(5946) ≤ 2973 → f(4053) ≥ 359.
  --          f(5946) ≤ 3*f(1982) + 2. f(1982) ≤ 990 → f(5946) ≤ 2972.
  --          f(4053) ≤ 3*f(1351) + 2. f(1351) ≤ (1351-2)/2 + f(2)/1 = 674.
  --            Actually f(1351) ≤ f(1349) + 1 ≤ ... ≤ f(3) + 674 = 675.
  --          f(4053) ≤ 3*675 + 2 = 2027. (Barely tighter.)

  -- This convergence is way too slow for a formalized proof. Let me try yet another approach.

  -- Maybe we should use the decomposition 1982 = 991 + 991.
  -- f(1982) ≤ 2*f(991) + 1.
  -- f(991) ≤ f(989) + 1 ≤ ... ≤ f(1) + 495 = 495. So f(1982) ≤ 991.
  -- f(991) = f(3*330 + 1) ≤ f(990) + 1 = f(3*330) + 1 ≤ 3*f(330) + 3.
  -- f(330) = f(3*110) ≤ 3*f(110) + 2.
  -- ...

  -- I think this problem is genuinely very hard to formalize without native_decide.
  -- Let me just try sorry for now and move on.
  sorry
