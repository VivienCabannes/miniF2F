import Mathlib
import Aesop
set_option maxHeartbeats 400000
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat

lemma round2_f_add_k (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987) : ∀ n, f (n + 1987) = f n + 1987 := by
  intro n
  have h2 : f (f (f n)) = f n + 1987 := by
    specialize h (f n)
    simpa using h
  have h3 : f (f n) = n + 1987 := h n
  have h4 : f (f (f n)) = f (n + 1987) := by
    have h5 : f (f n) = n + 1987 := h3
    have h6 : f (f (f n)) = f (n + 1987) := by
      rw [h5]
    exact h6
  linarith


lemma round2_f_add_qk (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987) : ∀ n q, f (n + q * 1987) = f n + q * 1987 := by
  have h1 : ∀ n, f (n + 1987) = f n + 1987 := round2_f_add_k f h
  intro n q
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h5 : f (n + (q + 1) * 1987) = f ((n + q * 1987) + 1987) := by ring
    have h6 : f ((n + q * 1987) + 1987) = f (n + q * 1987) + 1987 := by
      specialize h1 (n + q * 1987)
      simpa using h1
    have h7 : f (n + (q + 1) * 1987) = f (n + q * 1987) + 1987 := by linarith
    have h8 : f (n + q * 1987) + 1987 = f n + q * 1987 + 1987 := by linarith [ih]
    have h9 : f n + q * 1987 + 1987 = f n + (q + 1) * 1987 := by ring
    linarith


lemma round2_f_add_k_80628064 (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987) : ∀ n, f (n + 1987) = f n + 1987 := by
  intro n
  have h2 : f (f (f n)) = f n + 1987 := by
    specialize h (f n)
    simpa using h
  have h3 : f (f n) = n + 1987 := h n
  have h4 : f (f (f n)) = f (n + 1987) := by
    have h5 : f (f n) = n + 1987 := h3
    have h6 : f (f (f n)) = f (n + 1987) := by
      rw [h5]
    exact h6
  linarith


lemma round2_f_add_qk_8062869a (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987) : ∀ n q, f (n + q * 1987) = f n + q * 1987 := by
  have h1 : ∀ n, f (n + 1987) = f n + 1987 := round2_f_add_k_80628064 f h
  intro n q
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h5 : f (n + (q + 1) * 1987) = f ((n + q * 1987) + 1987) := by ring
    have h6 : f ((n + q * 1987) + 1987) = f (n + q * 1987) + 1987 := by
      specialize h1 (n + q * 1987)
      simpa using h1
    have h7 : f (n + (q + 1) * 1987) = f (n + q * 1987) + 1987 := by linarith
    have h8 : f (n + q * 1987) + 1987 = f n + q * 1987 + 1987 := by linarith [ih]
    have h9 : f n + q * 1987 + 1987 = f n + (q + 1) * 1987 := by ring
    linarith


lemma round3_f_f_mod_1987_80628c12 (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987) :
  ∀ n, f (f n) % 1987 = n % 1987 := by
  intro n
  have h1 : f (f n) = n + 1987 := h n
  omega


lemma round3_f_mod_1987_806290cc (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987) (h_add_qk : ∀ n q, f (n + q * 1987) = f n + q * 1987) :
  ∀ n, f n % 1987 = f (n % 1987) % 1987 := by
  intro n
  have h1 : n = (n % 1987) + (n / 1987) * 1987 := by omega
  have h2 : f n = f ((n % 1987) + (n / 1987) * 1987) := by
    congr
    <;> omega
  have h3 : f ((n % 1987) + (n / 1987) * 1987) = f (n % 1987) + (n / 1987) * 1987 := h_add_qk (n % 1987) (n / 1987)
  have h4 : f n = f (n % 1987) + (n / 1987) * 1987 := by linarith
  have h5 : f n % 1987 = (f (n % 1987) + (n / 1987) * 1987) % 1987 := by omega
  have h6 : (f (n % 1987) + (n / 1987) * 1987) % 1987 = f (n % 1987) % 1987 := by
    simp [Nat.add_mul_mod_self_right]
  omega


lemma round3_fixed_point_80629522 (P : ℕ → ℕ) (h_P_prop : ∀ n, n < 1987 → P (P n) = n) (h_P_bound : ∀ n, n < 1987 → P n < 1987) :
  ∃ n₀, n₀ < 1987 ∧ P n₀ = n₀ := by
  by_contra h_contra
  push_neg at h_contra
  have h1 : ∀ n, n < 1987 → P n ≠ n := by tauto
  let S := Finset.range 1987
  let A := Finset.filter (fun n => P n > n) S
  let B := Finset.filter (fun n => P n < n) S
  have hS_card : Finset.card S = 1987 := by simp [S]
  have h_A_union_B : A ∪ B = S := by
    apply Finset.ext
    intro n
    simp only [A, B, S, Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hnS
      have h2 : P n ≠ n := h_contra n hnS
      have h3 : P n > n ∨ P n < n := by omega
      cases h3 with
      | inl h3l =>
        exact Or.inl ⟨hnS, h3l⟩
      | inr h3r =>
        exact Or.inr ⟨hnS, h3r⟩
  have h_A_disjoint_B : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro n hnA hnB
    simp only [A, B, Finset.mem_filter] at hnA hnB
    linarith
  have h_card_S_eq_card_A_add_card_B : Finset.card S = Finset.card A + Finset.card B := by
    rw [← Finset.card_union_of_disjoint h_A_disjoint_B]
    rw [h_A_union_B]
  let g : ℕ → ℕ := fun n => P n
  have h_g_maps_A_to_B : ∀ n ∈ A, g n ∈ B := by
    intro n hnA
    simp only [A, S, Finset.mem_filter, Finset.mem_range] at hnA
    have hnS : n < 1987 := hnA.1
    have h_Pn_gt_n : P n > n := hnA.2
    have h_Pn_lt_1987 : P n < 1987 := h_P_bound n hnS
    have h_P_Pn_eq_n : P (P n) = n := h_P_prop n hnS
    simp only [B, S, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact h_Pn_lt_1987
    · have h_P_Pn_lt_Pn : P (P n) < P n := by linarith
      simpa [g] using h_P_Pn_lt_Pn
  have h_g_maps_B_to_A : ∀ n ∈ B, g n ∈ A := by
    intro n hnB
    simp only [B, S, Finset.mem_filter, Finset.mem_range] at hnB
    have hnS : n < 1987 := hnB.1
    have h_Pn_lt_n : P n < n := hnB.2
    have h_Pn_lt_1987 : P n < 1987 := h_P_bound n hnS
    have h_P_Pn_eq_n : P (P n) = n := h_P_prop n hnS
    simp only [A, S, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact h_Pn_lt_1987
    · have h_P_Pn_gt_Pn : P (P n) > P n := by linarith
      simpa [g] using h_P_Pn_gt_Pn
  have h_g_A_bij_B : ∀ n ∈ A, g (g n) = n := by
    intro n hnA
    simp only [A, S, Finset.mem_filter, Finset.mem_range] at hnA
    have hnS : n < 1987 := hnA.1
    have h_P_Pn_eq_n : P (P n) = n := h_P_prop n hnS
    simpa [g] using h_P_Pn_eq_n
  have h_card_A_eq_card_B : Finset.card A = Finset.card B := by
    apply Finset.card_congr (fun n _ => P n)
    · intro n hn
      exact h_g_maps_A_to_B n hn
    · intro n hn m hm h_eq
      have hnS : n < 1987 := by
        simp only [A, S, Finset.mem_filter, Finset.mem_range] at hn
        linarith
      have hmS : m < 1987 := by
        simp only [A, S, Finset.mem_filter, Finset.mem_range] at hm
        linarith
      have h_P_Pn_eq_n : P (P n) = n := h_P_prop n hnS
      have h_P_Pm_eq_m : P (P m) = m := h_P_prop m hmS
      have h_Pn_eq_Pm : P n = P m := by simpa [g] using h_eq
      have h_n_eq_m : n = m := by
        have h1 : P (P n) = P (P m) := by rw [h_Pn_eq_Pm]
        rw [h_P_Pn_eq_n, h_P_Pm_eq_m] at h1
        exact h1
      exact h_n_eq_m
    · intro m hm
      use P m
      have hmS : m < 1987 := by
        simp only [B, S, Finset.mem_filter, Finset.mem_range] at hm
        linarith
      have h_P_Pm_eq_m : P (P m) = m := h_P_prop m hmS
      have h_Pm_in_A : P m ∈ A := by
        have h_Pm_lt_1987 : P m < 1987 := h_P_bound m hmS
        have h_Pm_lt_m : P m < m := by
          simp only [B, S, Finset.mem_filter, Finset.mem_range] at hm
          linarith
        have h_P_Pm_gt_Pm : P (P m) > P m := by
          rw [h_P_Pm_eq_m]
          linarith
        simp only [A, S, Finset.mem_filter, Finset.mem_range]
        exact ⟨h_Pm_lt_1987, h_P_Pm_gt_Pm⟩
      refine ⟨h_Pm_in_A, ?_⟩
      exact h_P_Pm_eq_m
  omega


lemma round8_P_P_n_eq_n_mod_1987_8062996e (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987)
  (h_add_qk : ∀ n q, f (n + q * 1987) = f n + q * 1987) (n : ℕ) :
  f (f n % 1987) % 1987 = n % 1987 := by
  have h1 : f (f n) % 1987 = f ((f n) % 1987) % 1987 := by
    have h2 := round3_f_mod_1987_806290cc f h h_add_qk (f n)
    simpa using h2
  have h3 : f ((f n) % 1987) % 1987 = f (f n) % 1987 := by linarith
  have h4 : f (f n) % 1987 = n % 1987 := round3_f_f_mod_1987_80628c12 f h n
  linarith


lemma round8_P_P_n_eq_n_when_lt_1987_80629e14 (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987)
  (h_add_qk : ∀ n q, f (n + q * 1987) = f n + q * 1987) (n : ℕ) (hn : n < 1987) :
  f (f n % 1987) % 1987 = n := by
  have h1 : f (f n % 1987) % 1987 = n % 1987 := round8_P_P_n_eq_n_mod_1987_8062996e f h h_add_qk n
  have h2 : n % 1987 = n := Nat.mod_eq_of_lt hn
  rw [h2] at h1
  exact h1


lemma round8_P_n_lt_1987_8062a378 (f : ℕ → ℕ) (n : ℕ) : f n % 1987 < 1987 := by
  exact Nat.mod_lt (f n) (by norm_num)


lemma round8_exists_k_from_mod_eq_8062a7c4 (f : ℕ → ℕ) (n₀ : ℕ) (h_mod_eq : f n₀ % 1987 = n₀) :
  ∃ k : ℕ, f n₀ = k * 1987 + n₀ := by
  use f n₀ / 1987
  omega


lemma round8_two_k_eq_one_contradiction_8062acba (k : ℕ) (h : 2 * k * 1987 = 1987) : False := by
  have h1 : 2 * k * 1987 = 1987 := h
  have h2 : 2 * k = 1 := by nlinarith
  omega


lemma round1_contradiction (f : ℕ → ℕ) (h : ∀ n, f (f n) = n + 1987) : False := by
  have h_add_qk : ∀ n q, f (n + q * 1987) = f n + q * 1987 := round2_f_add_qk_8062869a f h
  have h_P_P_n : ∀ n, n < 1987 → f (f n % 1987) % 1987 = n := by
    intro n hn
    exact round8_P_P_n_eq_n_when_lt_1987_80629e14 f h h_add_qk n hn
  have h_P_n_lt : ∀ n, n < 1987 → f n % 1987 < 1987 := by
    intro n _
    exact round8_P_n_lt_1987_8062a378 f n
  have h_exists_n₀ : ∃ n₀, n₀ < 1987 ∧ f n₀ % 1987 = n₀ := by
    have h_P_P_n' : ∀ (n : ℕ), n < 1987 → (f (f n % 1987) % 1987) = n := by
      intro n hn
      exact h_P_P_n n hn
    have h_P_n_lt' : ∀ (n : ℕ), n < 1987 → (f n % 1987) < 1987 := by
      intro n hn
      exact h_P_n_lt n hn
    have h4 : ∃ n₀, n₀ < 1987 ∧ f n₀ % 1987 = n₀ := round3_fixed_point_80629522 (fun n => f n % 1987) h_P_P_n' h_P_n_lt'
    exact h4
  rcases h_exists_n₀ with ⟨n₀, hn₀_lt, h_n₀_mod_eq⟩
  rcases round8_exists_k_from_mod_eq_8062a7c4 f n₀ h_n₀_mod_eq with ⟨k, hk⟩
  have h_f_f_n₀ : f (f n₀) = n₀ + 1987 := h n₀
  have h_f_n₀_val : f n₀ = k * 1987 + n₀ := hk
  have h_f_f_n₀_subst : f (k * 1987 + n₀) = n₀ + 1987 := by
    have h1 : f (f n₀) = f (k * 1987 + n₀) := by
      have h2 : f n₀ = k * 1987 + n₀ := hk
      rw [h2]
    have h3 : f (f n₀) = n₀ + 1987 := h_f_f_n₀
    linarith
  have h_f_add : f (n₀ + k * 1987) = f n₀ + k * 1987 := h_add_qk n₀ k
  have h_f_k_add_n₀ : f (k * 1987 + n₀) = f n₀ + k * 1987 := by
    have h_comm : k * 1987 + n₀ = n₀ + k * 1987 := by ring
    have h : f (k * 1987 + n₀) = f (n₀ + k * 1987) := by rw [h_comm]
    linarith [h, h_f_add]
  have h_eq1 : f n₀ + k * 1987 = n₀ + 1987 := by linarith
  have h_eq2 : (k * 1987 + n₀) + k * 1987 = n₀ + 1987 := by
    have h : f n₀ = k * 1987 + n₀ := hk
    linarith
  have h_eq3 : 2 * k * 1987 + n₀ = n₀ + 1987 := by linarith
  have h_eq4 : 2 * k * 1987 = 1987 := by linarith
  exact round8_two_k_eq_one_contradiction_8062acba k h_eq4


theorem imo_1987_p4 (f : ℕ → ℕ) : ∃ n, f (f n) ≠ n + 1987 := by
  by_contra h₁
  push_neg at h₁
  exact round1_contradiction f h₁
