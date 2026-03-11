import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_136 (n : ℕ) (h₀ : 123 * n + 17 = 39500) : n = 321 := by
  have h₁ : 123 * n = 39500 - 17 := by
    -- Start with the given equation and simplify it by subtracting 17 from both sides.
    have h₁ : 123 * n = 39500 - 17 := by
      linarith
    -- The simplified equation shows that 123 * n equals 39500 minus 17.
    exact h₁
  
  have h₂ : n = (39500 - 17) / 123 := by
    apply Eq.symm
    -- We need to show that n is equal to (39500 - 17) / 123.
    -- Start by simplifying the equation 123 * n + 17 = 39500.
    norm_num at h₁ ⊢
    -- Simplify the equation using numerical computation to get 123 * n = 39483.
    <;> omega
    -- Use the omega tactic to solve for n, which will confirm that n = (39500 - 17) / 123.
    <;> omega
  
  have h₃ : (39500 - 17) / 123 = 321 := by
    simp_all only [mul_comm, mul_one, mul_div_cancel_left]
    -- Simplify the expressions by reducing the multiplication and division to their simplest forms.
    <;> norm_num
    -- Normalize the numerical expressions to confirm the result.
    <;> omega
    -- Use the omega tactic to solve the linear arithmetic problem and confirm the result.
    <;> ring
    -- Use the ring tactic to simplify the algebraic expressions and confirm the result.
    <;> linarith
  
  have h₄ : n = 321 := by
    simp_all only [mul_comm, mul_one, mul_div_cancel_left]
    -- Simplify all expressions using commutativity of multiplication, multiplication by one, and cancellation of multiplication and division.
    <;> omega
  
  -- This step is a redundant check to confirm the value of n, which is already determined by the previous steps.
  rw [h₄]