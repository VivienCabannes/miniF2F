import Mathlib
import Aesop
set_option maxHeartbeats 400000
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat

lemma round1_f_lt_f_succ (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) (h₂ : ∀ n, 0 < n → f n ≥ n) : ∀ n, 0 < n → f n < f (n + 1) := by
  intro n hn
  have h₃ : f n ≥ n := h₂ n hn
  have h₄ : 0 < f n := h₀ n
  have h₅ : f (f n) ≥ f n := h₂ (f n) h₄
  have h₆ : f (f n) < f (n + 1) := h₁ n hn
  linarith


lemma round1_f_le_n (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) (h₂ : ∀ n, 0 < n → f n ≥ n) (h₃ : ∀ n, 0 < n → f n < f (n + 1)) : ∀ n, 0 < n → f n ≤ n := by
  by_contra h
  push_neg at h
  have h₄ : ∃ n, 0 < n ∧ f n > n := h
  rcases h₄ with ⟨n, hn_pos, hfn_gt_n⟩
  have h₅ : f n > n := hfn_gt_n
  have h₆ : f n ≥ n + 1 := by linarith
  have h₇ : 0 < n + 1 := by linarith
  have h_lemma : ∀ k > 0, ∀ m, k ≤ m → f m ≥ f k := by
    intro k hk_pos
    intro m hm_ge_k
    induction m with
    | zero =>
      exfalso
      linarith
    | succ m ih =>
      by_cases h : k ≤ m
      · have ih' := ih h
        have h₁ : f (m + 1) > f m := h₃ m (by omega)
        have h₂ : f (m + 1) ≥ f m := by linarith
        linarith
      · have h₄ : k = m + 1 := by omega
        have h₅ : f (m + 1) ≥ f k := by
          have h₆ : f (m + 1) = f k := by
            have h₇ : m + 1 = k := by omega
            rw [h₇]
          linarith
        exact h₅
  have h₁₀ : 0 < n + 1 := by linarith
  have h₁₁ : n + 1 ≤ f n := by linarith
  have h₁₂ : f (f n) ≥ f (n + 1) := h_lemma (n + 1) h₁₀ (f n) h₁₁
  have h₁₃ : f (f n) < f (n + 1) := h₁ n hn_pos
  linarith


lemma round2_m_gt_1 (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1))
  (m : ℕ) (hm_pos : 0 < m) (hm_lt : f m < m)
  (hm_min : ∀ k : ℕ, 0 < k → k < m → f k ≥ k) : m > 1 := by
  by_contra h
  have h₂ : m ≤ 1 := by linarith
  have h₃ : m = 1 := by omega
  have h₄ : f m < m := hm_lt
  rw [h₃] at h₄
  have h₅ : f 1 < 1 := h₄
  have h₆ : f 1 = 0 := by omega
  have h₇ : 0 < f 1 := h₀ 1
  linarith


lemma round3_f_m_minus_1_eq_m_minus_1_adfca2f2 (f : ℕ → ℕ) (m : ℕ)
  (h_m_gt_1 : m > 1)
  (hm_min : ∀ k : ℕ, 0 < k → k < m → f k ≥ k)
  (h_f_m_minus_1_lt_m : f (m - 1) < m) : f (m - 1) = m - 1 := by
  have h1 : 0 < m - 1 := by omega
  have h2 : m - 1 < m := by omega
  have h3 : f (m - 1) ≥ m - 1 := hm_min (m - 1) h1 h2
  have h4 : f (m - 1) ≤ m - 1 := by omega
  omega


lemma round2_contradiction_from_f_m_minus_1_lt_m (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1))
  (m : ℕ) (hm_pos : 0 < m) (hm_lt : f m < m)
  (hm_min : ∀ k : ℕ, 0 < k → k < m → f k ≥ k) (h_m_gt_1 : m > 1)
  (h_f_m_minus_1_lt_m : f (m - 1) < m) : False := by
  have h_f_m_minus_1_eq_m_minus_1 : f (m - 1) = m - 1 := by
    exact round3_f_m_minus_1_eq_m_minus_1_adfca2f2 f m h_m_gt_1 hm_min h_f_m_minus_1_lt_m
  have h5 : 0 < m - 1 := by omega
  have h6 : f (f (m - 1)) < f ((m - 1) + 1) := h₁ (m - 1) h5
  have h7 : (m - 1) + 1 = m := by omega
  have h8 : f (f (m - 1)) < f m := by
    rw [h7] at h6
    exact h6
  have h9 : f (m - 1) < f m := by
    rw [h_f_m_minus_1_eq_m_minus_1] at h8
    exact h8
  have h10 : m - 1 < f m := by
    rw [h_f_m_minus_1_eq_m_minus_1] at h9
    exact h9
  have h11 : m ≤ f m := by omega
  linarith


lemma round3_min_val_c_is_lt_m (f : ℕ → ℕ) (m : ℕ) (hm_pos : 0 < m) (hm_lt : f m < m)
    (h₀ : ∀ n, 0 < f n) (c : ℕ) (hc : ∀ n : ℕ, m - 1 ≤ n → f n ≥ c) (hk : ∃ k : ℕ, m - 1 ≤ k ∧ f k = c) :
    c < m := by
  have h₁ : m - 1 ≤ m := by omega
  have h₂ : f m ≥ c := hc m h₁
  have h₃ : c ≤ f m := by linarith
  linarith


lemma round3_argmin_k_ge_m (f : ℕ → ℕ) (m : ℕ) (hm_pos : 0 < m) (hm_lt : f m < m)
    (h₀ : ∀ n, 0 < f n) (c : ℕ) (hc : ∀ n : ℕ, m - 1 ≤ n → f n ≥ c) (hk : ∃ k : ℕ, m - 1 ≤ k ∧ f k = c)
    (h_f_m_minus_1_ge_m : f (m - 1) ≥ m) (h_c_lt_m : c < m) :
    ∀ k : ℕ, m - 1 ≤ k → f k = c → k ≥ m := by
  intro k hk₁ hk₂
  by_contra h
  have h₁ : k < m := by linarith
  have h₂ : m - 1 ≤ k := hk₁
  have h₃ : k = m - 1 := by omega
  rw [h₃] at hk₂
  have h₄ : f (m - 1) = c := hk₂
  have h₅ : c < m := h_c_lt_m
  have h₆ : f (m - 1) < m := by linarith
  linarith


lemma round3_f_of_f_k_minus_1_lt_c (f : ℕ → ℕ) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) (m : ℕ) (hm_pos : 0 < m)
    (m_gt_1 : m > 1) (k : ℕ) (hk_ge_m : k ≥ m) (c : ℕ) (h_f_k_eq_c : f k = c) :
    f (f (k - 1)) < c := by
  have h₂ : 0 < k - 1 := by omega
  have h₃ : f (f (k - 1)) < f ((k - 1) + 1) := h₁ (k - 1) h₂
  have h₄ : (k - 1) + 1 = k := by omega
  have h₅ : f (f (k - 1)) < f k := by
    rw [h₄] at h₃
    exact h₃
  have h₆ : f k = c := h_f_k_eq_c
  linarith


lemma round3_f_k_minus_1_lt_m_minus_1 (f : ℕ → ℕ) (m : ℕ) (hm_pos : 0 < m) (m_gt_1 : m > 1) (c : ℕ)
    (h₀ : ∀ n, 0 < f n) (hc : ∀ n : ℕ, m - 1 ≤ n → f n ≥ c) (h_f_f_k_minus_1_lt_c : f (f (k - 1)) < c) :
    f (k - 1) < m - 1 := by
  by_contra h
  have h₁ : f (k - 1) ≥ m - 1 := by linarith
  have h₂ : f (f (k - 1)) ≥ c := hc (f (k - 1)) h₁
  linarith


lemma round1_main_ed1c31dc (f : ℕ → ℕ) (m : ℕ) (hm_pos : 0 < m) (h₀ : ∀ n, 0 < f n) :
    ∃ c : ℕ, (∀ n : ℕ, m - 1 ≤ n → f n ≥ c) ∧ (∃ k : ℕ, m - 1 ≤ k ∧ f k = c) := by
  have h1 : ∃ n : ℕ, ∃ k : ℕ, m - 1 ≤ k ∧ f k = n := by
    refine ⟨f (m - 1), m - 1, by simp⟩
  have hS_nonempty : ∃ n : ℕ, ∃ k : ℕ, m - 1 ≤ k ∧ f k = n := by tauto
  set S : Set ℕ := {n : ℕ | ∃ k : ℕ, m - 1 ≤ k ∧ f k = n} with hS_def
  have h2 : S.Nonempty := by
    rcases hS_nonempty with ⟨n, k, h3, h4⟩
    refine ⟨n, ?_⟩
    refine ⟨k, h3, h4⟩
  have h3 : ∃ c, c ∈ S ∧ ∀ n, n ∈ S → c ≤ n := by
    classical
    use Nat.find h2
    constructor
    · exact Nat.find_spec h2
    · intro n hn
      exact Nat.find_min' h2 hn
  rcases h3 with ⟨c, hc_in_S, h_all_n_in_S_le_c⟩
  have h4 : ∃ k : ℕ, m - 1 ≤ k ∧ f k = c := by
    have h41 : c ∈ S := hc_in_S
    have h42 : ∃ k : ℕ, m - 1 ≤ k ∧ f k = c := by
      simp only [hS_def, Set.mem_setOf_eq] at h41
      tauto
    tauto
  have h5 : ∀ n : ℕ, m - 1 ≤ n → f n ≥ c := by
    intro n hn
    have h6 : f n ∈ S := by
      simp only [hS_def, Set.mem_setOf_eq]
      refine ⟨n, hn, rfl⟩
    have h7 : c ≤ f n := h_all_n_in_S_le_c (f n) h6
    linarith
  refine ⟨c, ⟨h5, h4⟩⟩


lemma round3_min_of_f_ge_m_minus_1_exists (f : ℕ → ℕ) (m : ℕ) (hm_pos : 0 < m) (h₀ : ∀ n, 0 < f n) :
    ∃ c : ℕ, (∀ n : ℕ, m - 1 ≤ n → f n ≥ c) ∧ (∃ k : ℕ, m - 1 ≤ k ∧ f k = c) := by
  exact round1_main_ed1c31dc f m hm_pos h₀


lemma round4_new_counterexample_props (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1))
  (m : ℕ) (hm_pos : 0 < m) (hm_lt : f m < m)
  (hm_min : ∀ k : ℕ, 0 < k → k < m → f k ≥ k)
  (c : ℕ) (hc : ∀ n : ℕ, m - 1 ≤ n → f n ≥ c) (hk_exists : ∃ k : ℕ, m - 1 ≤ k ∧ f k = c)
  (h_f_m_minus_1_ge_m : f (m - 1) ≥ m) (h_c_lt_m : c < m)
  (k : ℕ) (hk_ge_m : k ≥ m) (h_f_k_eq_c : f k = c) (m_gt_1 : m > 1) :
  f (f (k - 1)) < f (k - 1) ∧ 0 < f (k - 1) ∧ f (k - 1) < m := by
  have h_f_f_k_minus_1_lt_c : f (f (k - 1)) < c := by
    exact round3_f_of_f_k_minus_1_lt_c f h₁ m hm_pos m_gt_1 k hk_ge_m c h_f_k_eq_c
  have h_f_k_minus_1_lt_m_minus_1 : f (k - 1) < m - 1 := by
    exact round3_f_k_minus_1_lt_m_minus_1 f m hm_pos m_gt_1 c h₀ hc h_f_f_k_minus_1_lt_c
  have h_f_k_minus_1_lt_m : f (k - 1) < m := by
    have h : m - 1 < m := by omega
    linarith
  have h_f_k_minus_1_pos : 0 < f (k - 1) := h₀ (k - 1)
  have h_f_k_minus_1_gt_c : f (k - 1) > c := by
    by_contra h_not_f_k_minus_1_gt_c
    have h_f_k_minus_1_le_c : f (k - 1) ≤ c := by linarith
    have h_k_minus_1_ge_m_minus_1 : m - 1 ≤ k - 1 := by omega
    have h_f_k_minus_1_ge_c : f (k - 1) ≥ c := hc (k - 1) h_k_minus_1_ge_m_minus_1
    have h_f_k_minus_1_eq_c : f (k - 1) = c := by linarith
    have h_f_c_lt_c : f c < c := by
      have h : f (f (k - 1)) < c := h_f_f_k_minus_1_lt_c
      have h2 : f (k - 1) = c := h_f_k_minus_1_eq_c
      have h3 : f (f (k - 1)) = f c := by
        rw [h2]
      have h4 : f c < c := by linarith
      exact h4
    have h_c_pos : 0 < c := by
      have h : 0 < f (k - 1) := h₀ (k - 1)
      have h2 : f (k - 1) = c := h_f_k_minus_1_eq_c
      linarith
    have h_f_c_ge_c : f c ≥ c := hm_min c h_c_pos (by linarith)
    linarith
  exact ⟨by linarith, by linarith, by linarith⟩


lemma round4_contradiction_from_z_props (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1))
  (m : ℕ) (hm_pos : 0 < m) (hm_lt : f m < m)
  (hm_min : ∀ k : ℕ, 0 < k → k < m → f k ≥ k)
  (z : ℕ) (h_f_z_lt_z : f z < z) (h_z_pos : 0 < z) (h_z_lt_m : z < m) : False := by
  have h_contradiction : f z ≥ z := hm_min z h_z_pos h_z_lt_m
  linarith


lemma round5_h_ge (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) : ∀ n, 0 < n → f n ≥ n := by
  intro n hn_pos
  by_contra h_neg
  push_neg at h_neg
  have h_exists : ∃ m : ℕ, 0 < m ∧ f m < m := by
    exact ⟨n, hn_pos, h_neg⟩
  set m := Nat.find h_exists with hm_def
  have hm_spec : 0 < m ∧ f m < m := Nat.find_spec h_exists
  have hm_pos : 0 < m := hm_spec.1
  have hm_lt : f m < m := hm_spec.2
  have hm_min : ∀ k : ℕ, 0 < k → k < m → f k ≥ k := by
    intro k hk_pos hk_lt_m
    have h_not_spec : ¬(0 < k ∧ f k < k) := by
      intro h_k_spec
      have h_k_lt_m' : k < m := hk_lt_m
      have h_contra := Nat.find_min h_exists h_k_lt_m' h_k_spec
      exact h_contra
    have h_f_k_ge_k : f k ≥ k := by
      by_contra h_f_k_lt_k
      have h_f_k_lt_k' : f k < k := by linarith
      have h_contra : 0 < k ∧ f k < k := ⟨hk_pos, h_f_k_lt_k'⟩
      exact h_not_spec h_contra
    exact h_f_k_ge_k
  have m_gt_1 : m > 1 := round2_m_gt_1 f h₀ h₁ m hm_pos hm_lt hm_min
  by_cases h_f_m_minus_1_lt_m : f (m - 1) < m
  · exact round2_contradiction_from_f_m_minus_1_lt_m f h₀ h₁ m hm_pos hm_lt hm_min m_gt_1 h_f_m_minus_1_lt_m
  · have h_f_m_minus_1_ge_m : f (m - 1) ≥ m := by linarith
    have h_min_exists : ∃ c : ℕ, (∀ n : ℕ, m - 1 ≤ n → f n ≥ c) ∧ (∃ k : ℕ, m - 1 ≤ k ∧ f k = c) :=
      round3_min_of_f_ge_m_minus_1_exists f m hm_pos h₀
    rcases h_min_exists with ⟨c, hc, hk_hyp⟩
    have hk_for_argmin : ∃ k : ℕ, m - 1 ≤ k ∧ f k = c := hk_hyp
    have hk_exists_for_props : ∃ k : ℕ, m - 1 ≤ k ∧ f k = c := hk_hyp
    have h_c_lt_m : c < m := round3_min_val_c_is_lt_m f m hm_pos hm_lt h₀ c hc hk_hyp
    rcases hk_hyp with ⟨k, hk_ge_m_minus_1, h_f_k_eq_c⟩
    have h_forall_k_ge_m : ∀ k' : ℕ, m - 1 ≤ k' → f k' = c → k' ≥ m :=
      round3_argmin_k_ge_m f m hm_pos hm_lt h₀ c hc hk_for_argmin h_f_m_minus_1_ge_m h_c_lt_m
    have hk_ge_m : k ≥ m := h_forall_k_ge_m k hk_ge_m_minus_1 h_f_k_eq_c
    have h_new_counterexample_props : f (f (k - 1)) < f (k - 1) ∧ 0 < f (k - 1) ∧ f (k - 1) < m :=
      round4_new_counterexample_props f h₀ h₁ m hm_pos hm_lt hm_min c hc hk_exists_for_props h_f_m_minus_1_ge_m h_c_lt_m k hk_ge_m h_f_k_eq_c m_gt_1
    have h_f_z_lt_z : f (f (k - 1)) < f (k - 1) := h_new_counterexample_props.1
    have h_z_pos : 0 < f (k - 1) := h_new_counterexample_props.2.1
    have h_z_lt_m : f (k - 1) < m := h_new_counterexample_props.2.2
    exact round4_contradiction_from_z_props f h₀ h₁ m hm_pos hm_lt hm_min (f (k - 1)) h_f_z_lt_z h_z_pos h_z_lt_m


theorem imo_1977_p6 (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) :
    ∀ n, 0 < n → f n = n := by
  have h_ge : ∀ n, 0 < n → f n ≥ n := round5_h_ge f h₀ h₁
  have h_strict_inc : ∀ n, 0 < n → f n < f (n + 1) := round1_f_lt_f_succ f h₀ h₁ h_ge
  have h_le : ∀ n, 0 < n → f n ≤ n := round1_f_le_n f h₀ h₁ h_ge h_strict_inc
  intro n hn
  have h1 : f n ≥ n := h_ge n hn
  have h2 : f n ≤ n := h_le n hn
  linarith
