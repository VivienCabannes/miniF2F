import Mathlib

open BigOperators Real Nat Topology Rat

/-- The witness function for IMO 1993 P5: given n with Zeckendorf representation
    n = fib(a_1) + fib(a_2) + ... + fib(a_k), define f(n) = fib(a_1+1) + ... + fib(a_k+1).
    This satisfies f(1) = 2, f(f(n)) = f(n) + n, and is strictly increasing. -/
private def imo_f (n : ℕ) : ℕ := ((Nat.zeckendorf n).map (fun a => Nat.fib (a + 1))).sum

private lemma shift_isZeckendorfRep {l : List ℕ} (h : l.IsZeckendorfRep) :
    (l.map (· + 1)).IsZeckendorfRep := by
  unfold List.IsZeckendorfRep at *
  induction l with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    exact List.IsChain.singleton 0
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append] at *
      have : 0 + 2 ≤ a := by cases h with | cons_cons hr _ => exact hr
      exact List.IsChain.cons_cons (by omega) (List.IsChain.singleton 0)
    | cons b t' =>
      simp only [List.map_cons, List.cons_append] at *
      have hab : b + 2 ≤ a := by cases h with | cons_cons hr _ => exact hr
      have ht : List.IsChain (fun a b => b + 2 ≤ a) (b :: (t' ++ [0])) := by
        cases h with | cons_cons _ ht => exact ht
      exact List.IsChain.cons_cons (by omega) (ih ht)

private lemma imo_f_eq (n : ℕ) :
    imo_f n = (List.map Nat.fib ((Nat.zeckendorf n).map (· + 1))).sum := by
  unfold imo_f; congr 1; rw [List.map_map]; rfl

private lemma zeckendorf_imo_f (n : ℕ) :
    Nat.zeckendorf (imo_f n) = (Nat.zeckendorf n).map (· + 1) := by
  rw [imo_f_eq]
  exact Nat.zeckendorf_sum_fib (shift_isZeckendorfRep (Nat.isZeckendorfRep_zeckendorf n))

private lemma imo_f_comp (n : ℕ) : imo_f (imo_f n) = imo_f n + n := by
  show ((Nat.zeckendorf (imo_f n)).map (fun a => Nat.fib (a + 1))).sum = imo_f n + n
  rw [zeckendorf_imo_f, List.map_map]
  show ((Nat.zeckendorf n).map (fun a => Nat.fib (a + 1 + 1))).sum = imo_f n + n
  simp_rw [Nat.fib_add_two]
  rw [List.sum_map_add]
  rw [Nat.sum_zeckendorf_fib]
  unfold imo_f; ring

private lemma imo_f_one : imo_f 1 = 2 := by
  norm_num [imo_f, Nat.zeckendorf_succ, Nat.greatestFib, Nat.findGreatest]

private lemma sum_shift_eq {l : List ℕ} :
    (l.map (fun x => Nat.fib (x + 1))).sum = (List.map Nat.fib (l.map (· + 1))).sum := by
  congr 1; rw [List.map_map]; rfl

private lemma sum_shift_zeckendorf_lt {a : ℕ} {rest : List ℕ}
    (h : (a :: rest).IsZeckendorfRep) :
    (List.map (fun x => Nat.fib (x + 1)) (a :: rest)).sum < Nat.fib (a + 2) := by
  rw [sum_shift_eq]
  exact (shift_isZeckendorfRep h).sum_fib_lt (by simp)

private lemma fib_succ_le_sum_shift {a : ℕ} {rest : List ℕ} :
    Nat.fib (a + 1) ≤ (List.map (fun x => Nat.fib (x + 1)) (a :: rest)).sum := by
  simp [List.sum_cons]

private lemma isZeckendorfRep_tail {a : ℕ} {rest : List ℕ}
    (h : (a :: rest).IsZeckendorfRep) : rest.IsZeckendorfRep := by
  unfold List.IsZeckendorfRep at *
  simp only [List.cons_append] at h
  exact h.tail

private lemma sum_fib_pos_of_ne_nil {l : List ℕ} (h : l.IsZeckendorfRep) (hne : l ≠ []) :
    0 < (l.map Nat.fib).sum := by
  cases l with
  | nil => contradiction
  | cons a rest =>
    simp only [List.map_cons, List.sum_cons]
    have ha : 2 ≤ a := by
      unfold List.IsZeckendorfRep at h
      simp only [List.cons_append] at h
      cases rest with
      | nil => simp only [List.nil_append] at h; cases h with | cons_cons hr _ => omega
      | cons b _ => cases h with | cons_cons hr _ => omega
    have := Nat.fib_pos.mpr (show 0 < a by omega)
    omega

private lemma zeckendorf_shift_strict_mono :
    ∀ (l₁ l₂ : List ℕ),
    l₁.IsZeckendorfRep → l₂.IsZeckendorfRep →
    (l₁.map Nat.fib).sum < (l₂.map Nat.fib).sum →
    (l₁.map (fun x => Nat.fib (x + 1))).sum < (l₂.map (fun x => Nat.fib (x + 1))).sum := by
  intro l₁ l₂ h₁ h₂ hlt
  induction l₁ generalizing l₂ with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    cases l₂ with
    | nil => simp only [List.map_nil, List.sum_nil] at hlt; omega
    | cons b rest₂ =>
      simp only [List.map_cons, List.sum_cons]
      have := Nat.fib_pos.mpr (show 0 < b + 1 by omega)
      omega
  | cons a rest₁ ih =>
    cases l₂ with
    | nil =>
      simp only [List.map_nil, List.sum_nil] at hlt
      have := sum_fib_pos_of_ne_nil h₁ (by simp)
      omega
    | cons b rest₂ =>
      by_cases hab : a < b
      · calc (List.map (fun x => Nat.fib (x + 1)) (a :: rest₁)).sum
            < Nat.fib (a + 2) := sum_shift_zeckendorf_lt h₁
          _ ≤ Nat.fib (b + 1) := Nat.fib_mono (by omega)
          _ ≤ (List.map (fun x => Nat.fib (x + 1)) (b :: rest₂)).sum := fib_succ_le_sum_shift
      · by_cases hba : b < a
        · have : (List.map Nat.fib (b :: rest₂)).sum < (List.map Nat.fib (a :: rest₁)).sum :=
            calc (List.map Nat.fib (b :: rest₂)).sum
                < Nat.fib (b + 1) := h₂.sum_fib_lt (by simp)
              _ ≤ Nat.fib a := Nat.fib_mono (by omega)
              _ ≤ (List.map Nat.fib (a :: rest₁)).sum := by simp [List.sum_cons]
          omega
        · have heq : a = b := by omega
          subst heq
          simp only [List.map_cons, List.sum_cons] at hlt ⊢
          have hlt' : (rest₁.map Nat.fib).sum < (rest₂.map Nat.fib).sum := by omega
          have := ih rest₂ (isZeckendorfRep_tail h₁) (isZeckendorfRep_tail h₂) hlt'
          omega

private lemma imo_f_strict_mono (n : ℕ) : imo_f n < imo_f (n + 1) := by
  unfold imo_f
  apply zeckendorf_shift_strict_mono
  · exact Nat.isZeckendorfRep_zeckendorf n
  · exact Nat.isZeckendorfRep_zeckendorf (n + 1)
  · rw [Nat.sum_zeckendorf_fib, Nat.sum_zeckendorf_fib]
    omega

theorem imo_1993_p5 : ∃ f : ℕ → ℕ, f 1 = 2 ∧ ∀ n, f (f n) = f n + n ∧ ∀ n, f n < f (n + 1) := by
  exact ⟨imo_f, imo_f_one, fun n => ⟨imo_f_comp n, fun m => imo_f_strict_mono m⟩⟩
