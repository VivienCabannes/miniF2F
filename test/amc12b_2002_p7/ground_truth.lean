import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem amc12b_2002_p7
  (a b c : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : b = a + 1)
  (h₂ : c = b + 1)
  (h₃ : a * b * c = 8 * (a + b + c)) :
  a^2 + (b^2 + c^2) = 77 := by
  have h₄ : c = a + 2 := by
    have h₄₁ : c = a + 2 := by
      rw [h₂, h₁]
      <;> ring_nf
      <;> omega
    exact h₄₁
  
  have h₅ : a * (a + 1) * (a + 2) = 24 * (a + 1) := by
    have h₅₁ : a * b * c = 8 * (a + b + c) := h₃
    have h₅₂ : b = a + 1 := h₁
    have h₅₃ : c = a + 2 := h₄
    rw [h₅₂, h₅₃] at h₅₁
    ring_nf at h₅₁ ⊢
    <;>
    (try omega) <;>
    (try nlinarith) <;>
    (try ring_nf at h₅₁ ⊢ <;> nlinarith)
    <;>
    (try
      {
        cases a with
        | zero => contradiction
        | succ a' =>
          cases a' with
          | zero => contradiction
          | succ a'' =>
            cases a'' with
            | zero => contradiction
            | succ a''' =>
              cases a''' with
              | zero => contradiction
              | succ a'''' =>
                cases a'''' with
                | zero =>
                  norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                | succ a''''' =>
                  cases a''''' with
                  | zero =>
                    norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                  | succ a'''''' =>
                    cases a'''''' with
                    | zero =>
                      norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                    | succ a''''''' =>
                      cases a''''''' with
                      | zero =>
                        norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                      | succ a'''''''' =>
                        cases a'''''''' with
                        | zero =>
                          norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                        | succ a''''''''' =>
                          cases a''''''''' with
                          | zero =>
                            norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                          | succ a'''''''''' =>
                            cases a'''''''''' with
                            | zero =>
                              norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                            | succ a''''''''''' =>
                              cases a''''''''''' with
                              | zero =>
                                norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                              | succ a'''''''''''' =>
                                cases a'''''''''''' with
                                | zero =>
                                  norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                                | succ a''''''''''''' =>
                                  cases a''''''''''''' with
                                  | zero =>
                                    norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                                  | succ a'''''''''''''' =>
                                    cases a'''''''''''''' with
                                    | zero =>
                                      norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                                    | succ a''''''''''''''' =>
                                      cases a''''''''''''''' with
                                      | zero =>
                                        norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                                      | succ a'''''''''''''''' =>
                                        cases a'''''''''''''''' with
                                        | zero =>
                                          norm_num at h₅₁ ⊢ <;> ring_nf at h₅₁ ⊢ <;> nlinarith
                                        | succ a''''''''''''''''' =>
                                          simp_all [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
                                          <;> ring_nf at *
                                          <;> nlinarith
      })
    <;>
    omega
  
  have h₆ : a = 4 := by
    have h₆₁ : a ≤ 6 := by
      by_contra h
      have h₆₂ : a ≥ 7 := by
        omega
      have h₆₃ : a * (a + 1) * (a + 2) > 24 * (a + 1) := by
        have h₆₄ : a ≥ 7 := h₆₂
        have h₆₅ : a * (a + 1) * (a + 2) > 24 * (a + 1) := by
          have h₆₆ : a * (a + 1) * (a + 2) = a * (a + 1) * (a + 2) := rfl
          have h₆₇ : 24 * (a + 1) = 24 * (a + 1) := rfl
          have h₆₈ : a * (a + 1) * (a + 2) > 24 * (a + 1) := by
            have h₆₉ : a * (a + 2) ≥ 7 * 9 := by
              nlinarith
            nlinarith
          exact h₆₈
        exact h₆₅
      linarith
    interval_cases a <;> norm_num at h₅ ⊢ <;>
    (try omega) <;>
    (try nlinarith)
  
  have h₇ : b = 5 := by
    rw [h₁, h₆]
    <;> norm_num
  
  have h₈ : c = 6 := by
    rw [h₄, h₆]
    <;> norm_num
  
  have h₉ : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
    rw [h₆, h₇, h₈]
    <;> norm_num
  
  exact h₉