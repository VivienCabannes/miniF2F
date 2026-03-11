import Mathlib
import Aesop

set_option maxHeartbeats 3200000

open BigOperators Real Nat Topology Rat
open Nat.ArithmeticFunction in

-- Helper: card of divisors of p^k * m where p is prime and p doesn't divide m
lemma card_divisors_prime_pow_mul {p k m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hcop : Nat.Coprime (p ^ k) m) :
    #(p ^ k * m).divisors = (k + 1) * #m.divisors := by
  rw [Nat.Coprime.card_divisors_mul hcop]
  simp [Nat.divisors_prime_pow hp, Finset.card_range]

-- Helper: if n > 0 then 2 * n > 0
-- Helper: extract 2-adic valuation
-- We'll use the approach: n = 2^a * n', where n' is odd.
-- Then 2*n = 2^(a+1) * n' and d(2*n) = (a+2) * d(n').

theorem mathd_numbertheory_709 (n : ℕ) (h₀ : 0 < n) (h₁ : #(Nat.divisors (2 * n)) = 28)
  (h₂ : #(Nat.divisors (3 * n)) = 30) : #(Nat.divisors (6 * n)) = 35 := by
  -- Let a = v₂(n), then n = 2^a * n₁ where n₁ is odd.
  -- 2n = 2^(a+1) * n₁, and d(2n) = (a+2) * d(n₁) = 28.
  -- Similarly, let b = v₃(n₁), then n₁ = 3^b * m where m is coprime to 6.
  -- d(2n) = (a+2) * (b+1) * d(m) = 28
  -- d(3n) = (a+1) * (b+2) * d(m) = 30
  -- d(6n) = (a+2) * (b+2) * d(m) = ?
  -- Unique solution: a=5, b=3, d(m)=1
  -- d(6n) = 7 * 5 * 1 = 35
  --
  -- Instead of formalizing the full decomposition, let's use the identity
  -- d(n) * d(6n) = d(2n) * d(3n) and show d(n) = 24.
  -- Then d(6n) = 28 * 30 / 24 = 35.
  --
  -- Actually, let's try to prove d(2n)*d(3n) = d(n)*d(6n) directly.
  -- d(2n)*d(3n) = σ₀(2n)*σ₀(3n).
  -- Using the multiplicative factorization, for each prime p:
  --   (2n).factorization p + (3n).factorization p
  -- = if p=2 then n.fact(2)+1 + n.fact(2) else if p=3 then n.fact(3) + n.fact(3)+1 else 2*n.fact(p)
  -- Similarly for n and 6n.
  -- The product telescopes nicely.
  --
  -- Let me try a completely different strategy: directly compute using omega/decide
  -- after establishing enough bounds.
  sorry
