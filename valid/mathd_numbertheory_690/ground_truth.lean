import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_690 :
    IsLeast { a : ℕ | 0 < a ∧ a ≡ 2 [MOD 3] ∧ a ≡ 4 [MOD 5] ∧ a ≡ 6 [MOD 7] ∧ a ≡ 8 [MOD 9] } 314 := by
  -- Use the `refine'` tactic to construct the proof step by step.
  refine' ⟨by decide, fun a ⟨ha₁, ha₂, ha₃, ha₄, ha₅⟩ => _⟩
  -- Normalize the congruences using `ModEq` and `Nat.modEq_iff_dvd`.
  norm_num [ModEq, Nat.modEq_iff_dvd] at ha₂ ha₃ ha₄ ha₅
  -- Use the `omega` tactic to solve the system of linear congruences.
  omega