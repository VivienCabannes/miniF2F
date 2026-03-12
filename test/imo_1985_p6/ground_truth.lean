import Mathlib

open BigOperators Real Nat Topology Rat

theorem imo_1985_p6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ x, f 1 x = x)
  (h₁ : ∀ x n, f (n + 1) x = f n x * (f n x + 1 / n)) :
  ∃! a, ∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  -- =====================================================
  -- BASIC PROPERTIES OF THE RECURRENCE
  -- =====================================================
  -- f n 0 = 0 for n ≥ 1
  have hf0 : ∀ n, 0 < n → f n 0 = 0 := by
    intro n hn; induction n with
    | zero => omega
    | succ n ih => cases n with
      | zero => rw [h₀]; exact NNReal.coe_zero
      | succ n => rw [h₁]; rw [ih (by omega)]; ring
  -- f is continuous in x for each n ≥ 1
  have hcont : ∀ n, 0 < n → Continuous (f n) := by
    intro n hn; induction n with
    | zero => omega
    | succ n ih => cases n with
      | zero =>
        show Continuous (f 1)
        rw [show f 1 = (fun x : NNReal => (x : ℝ)) from funext h₀]
        exact NNReal.continuous_coe
      | succ n =>
        show Continuous (f (n + 2))
        rw [show f (n + 2) = fun x => f (n + 1) x * (f (n + 1) x + 1 / (↑(n + 1) : ℝ))
            from funext (fun x => h₁ x (n + 1))]
        exact (ih (by omega)).mul ((ih (by omega)).add continuous_const)
  -- f n x ≥ 0 for x : NNReal, n ≥ 1
  have hfnn : ∀ n, 0 < n → ∀ x : NNReal, 0 ≤ f n x := by
    intro n hn; induction n with
    | zero => omega
    | succ n ih => intro x; cases n with
      | zero => rw [h₀]; exact x.coe_nonneg
      | succ n =>
        rw [h₁]; apply mul_nonneg (ih (by omega) x)
        linarith [ih (by omega) x,
          show (0 : ℝ) < 1 / (↑(n + 1) : ℝ) from by positivity]
  -- f n is strictly monotone for n ≥ 1
  have hfmono : ∀ n, 0 < n → StrictMono (f n) := by
    intro n hn; induction n with
    | zero => omega
    | succ n ih => cases n with
      | zero =>
        intro a b hab; simp only [h₀]; exact NNReal.coe_lt_coe.mpr hab
      | succ n =>
        intro a b hab
        show f (n + 1 + 1) a < f (n + 1 + 1) b
        rw [h₁ a (n + 1), h₁ b (n + 1)]
        nlinarith [hfnn (n + 1) (by omega) a, hfnn (n + 1) (by omega) b,
          ih (by omega) hab, show (0 : ℝ) < 1 / (↑(n + 1) : ℝ) from by positivity]
  -- f n x > 0 when x > 0
  have hfpos : ∀ n, 0 < n → ∀ x : NNReal, (0 : ℝ) < x → 0 < f n x := by
    intro n hn; induction n with
    | zero => omega
    | succ n ih => intro x hx; cases n with
      | zero => rw [h₀]; exact hx
      | succ n =>
        rw [h₁]; apply mul_pos (ih (by omega) x hx)
        linarith [le_of_lt (ih (by omega) x hx),
          show (0 : ℝ) < 1 / (↑(n + 1) : ℝ) from by positivity]
  -- =====================================================
  -- THE RECURRENCE DIFFERENCE IDENTITY
  -- =====================================================
  -- f_{n+1}(b) - f_{n+1}(a) = (f_n(b) - f_n(a)) * (f_n(a) + f_n(b) + 1/n)
  have hdiff : ∀ n a b, f (n + 1) b - f (n + 1) a =
      (f n b - f n a) * (f n a + f n b + 1 / (↑n : ℝ)) := by
    intro n a b; rw [h₁ b n, h₁ a n]; ring
  -- =====================================================
  -- UNIQUENESS
  -- =====================================================
  have huniq : ∀ a b : NNReal,
      (∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1) →
      (∀ n, 0 < n → 0 < f n b ∧ f n b < f (n + 1) b ∧ f (n + 1) b < 1) →
      a = b := by
    intro a b ha hb
    by_contra hab_ne
    -- Upper bounds: f_n(a) < 1 and f_n(b) < 1
    have hfa_upper : ∀ n, 0 < n → f n a < 1 := fun n hn =>
      lt_trans (ha n hn).2.1 (ha n hn).2.2
    have hfb_upper : ∀ n, 0 < n → f n b < 1 := fun n hn =>
      lt_trans (hb n hn).2.1 (hb n hn).2.2
    -- Lower bounds: 1 - 1/n < f_n(a) and 1 - 1/n < f_n(b)
    -- Proof: f_n(a) < f_{n+1}(a) = f_n(a)*(f_n(a) + 1/n), with f_n(a) > 0,
    -- gives 1 < f_n(a) + 1/n, i.e., f_n(a) > 1 - 1/n.
    have hfa_lower : ∀ n : ℕ, 0 < n → 1 - 1 / (↑n : ℝ) < f n a := by
      intro n hn
      have hpos := (ha n hn).1
      have hlt := (ha n hn).2.1
      rw [h₁] at hlt; nlinarith
    have hfb_lower : ∀ n : ℕ, 0 < n → 1 - 1 / (↑n : ℝ) < f n b := by
      intro n hn
      have hpos := (hb n hn).1
      have hlt := (hb n hn).2.1
      rw [h₁] at hlt; nlinarith
    -- |f_n(b) - f_n(a)| < 1/n (both in (1-1/n, 1))
    have hbound : ∀ n : ℕ, 0 < n → |f n b - f n a| < 1 / (↑n : ℝ) := by
      intro n hn
      rw [abs_lt]; constructor <;> linarith [hfa_lower n hn, hfb_upper n hn,
        hfa_upper n hn, hfb_lower n hn]
    -- f_n(a) + f_n(b) + 1/n ≥ 1
    have hfactor : ∀ n : ℕ, 0 < n → 1 ≤ f n a + f n b + 1 / (↑n : ℝ) := by
      intro n hn
      have h4 : 1 / (↑n : ℝ) ≤ 1 := by
        rw [div_le_one (Nat.cast_pos.mpr hn)]; exact Nat.one_le_cast.mpr hn
      linarith [hfa_lower n hn, hfb_lower n hn]
    -- |f_{n+1}(b) - f_{n+1}(a)| ≥ |f_n(b) - f_n(a)|
    have hgrow : ∀ n : ℕ, 0 < n → |f n b - f n a| ≤ |f (n + 1) b - f (n + 1) a| := by
      intro n hn
      rw [hdiff n a b, abs_mul]
      calc |f n b - f n a| = |f n b - f n a| * 1 := (mul_one _).symm
        _ ≤ |f n b - f n a| * |f n a + f n b + 1 / ↑n| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg (by linarith [hfactor n hn])]; exact hfactor n hn
    -- By induction: |f_n(b) - f_n(a)| ≥ |↑b - ↑a| for all n ≥ 1
    have hgrow_all : ∀ n : ℕ, 0 < n → |(↑b : ℝ) - ↑a| ≤ |f n b - f n a| := by
      intro n hn; induction n with
      | zero => omega
      | succ n ih => cases n with
        | zero => simp only [h₀]; exact le_refl _
        | succ n =>
          calc |(↑b : ℝ) - ↑a| ≤ |f (n + 1) b - f (n + 1) a| := ih (by omega)
            _ ≤ |f (n + 1 + 1) b - f (n + 1 + 1) a| := hgrow (n + 1) (by omega)
    -- |↑b - ↑a| < 1/n for all n ≥ 1
    have hsmall : ∀ n : ℕ, 0 < n → |(↑b : ℝ) - ↑a| < 1 / (↑n : ℝ) :=
      fun n hn => lt_of_le_of_lt (hgrow_all n hn) (hbound n hn)
    -- Therefore ↑b = ↑a, contradicting a ≠ b
    have : (↑b : ℝ) = ↑a := by
      by_contra hne
      have hpos : 0 < |(↑b : ℝ) - ↑a| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / |(↑b : ℝ) - ↑a|)
      have hn_pos : 0 < n := by
        by_contra h; push_neg at h; interval_cases n
        simp at hn; linarith [div_pos one_pos hpos]
      have h1 := hsmall n hn_pos
      have h2 : 1 / (↑n : ℝ) ≤ |(↑b : ℝ) - ↑a| := by
        rw [div_le_iff₀ (Nat.cast_pos.mpr hn_pos)]
        rw [div_lt_iff₀ hpos] at hn; linarith
      linarith
    exact hab_ne (NNReal.coe_injective this.symm)
  -- =====================================================
  -- EXISTENCE (via nested intervals / Cantor's theorem)
  -- =====================================================
  -- The existence argument requires:
  -- 1. By IVT, for each n ≥ 1 there exists b_n with f n (b_n) = 1
  --    (using continuity of f_n, f_n(0) = 0, and f_n(M) > 1 for large M)
  -- 2. Define closed sets C_n = {a : NNReal | ∀ k ≤ n, k ≥ 1 → f k a ≤ 1 ∧ 1-1/k ≤ f k a}
  -- 3. Show C_n is compact (closed and bounded, since a ∈ C_n implies a ≤ b_1)
  -- 4. Show C_n is nonempty (by IVT, the midpoint of (a_n, b_n) works)
  -- 5. Show C_{n+1} ⊆ C_n (monotonicity)
  -- 6. By Cantor's theorem, ∩ C_n is nonempty
  -- 7. Any a in ∩ C_n satisfies 1-1/n ≤ f_n(a) ≤ 1 for all n
  -- 8. Upgrade to strict inequalities using the uniqueness argument:
  --    if f_n(a) = 1 for some n, then f_{n+1}(a) = 1+1/n > 1, contradicting f_{n+1}(a) ≤ 1
  --    if f_n(a) = 1-1/n for some n, then f_{n+1}(a) = (1-1/n) < 1-1/(n+1),
  --    contradicting 1-1/(n+1) ≤ f_{n+1}(a)
  --
  -- This full formalization is extremely involved (hundreds of lines of Lean 4)
  -- and is left as sorry.
  have hexist : ∃ a, ∀ n, 0 < n →
      0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
    -- Define closed sets C_n for n ≥ 1
    -- C n = {a : NNReal | ∀ k, 1 ≤ k → k ≤ n → 1 - 1/k ≤ f k a ∧ f k a ≤ 1}
    set C : ℕ → Set NNReal := fun n =>
      {a | ∀ k : ℕ, 0 < k → k ≤ n → 1 - 1 / (↑k : ℝ) ≤ f k a ∧ f k a ≤ 1}
    -- C n is closed (finite intersection of preimages of closed sets under continuous f k)
    have hC_closed : ∀ n, IsClosed (C n) := by
      intro n; induction n with
      | zero =>
        convert isClosed_univ; ext a; simp [C]; intro k hk; omega
      | succ n ih =>
        have : C (n + 1) = C n ∩
            {a | 1 - 1 / (↑(n + 1) : ℝ) ≤ f (n + 1) a ∧ f (n + 1) a ≤ 1} := by
          ext a; simp only [C, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro ha
            exact ⟨fun k hk hkn => ha k hk (by omega),
                   ha (n + 1) (by omega) (le_refl _)⟩
          · intro ⟨ha, hk⟩ k hk' hkn
            by_cases h : k ≤ n
            · exact ha k hk' h
            · have : k = n + 1 := by omega
              rw [this]; exact hk
        rw [this]
        exact ih.inter ((isClosed_le continuous_const (hcont (n + 1) (by omega))).inter
          (isClosed_le (hcont (n + 1) (by omega)) continuous_const))
    -- C n is decreasing
    have hC_mono : ∀ n, C (n + 1) ⊆ C n := by
      intro n a ha k hk hkn
      exact ha k hk (by omega)
    -- For n ≥ 1, C n ⊆ [0, 1] (since f 1 a = a ≤ 1)
    have hC_bounded : ∀ n, 1 ≤ n → C n ⊆ Set.Icc 0 1 := by
      intro n hn a ha
      refine ⟨bot_le, ?_⟩
      have := (ha 1 one_pos hn).2
      rw [h₀] at this
      exact_mod_cast this
    -- C n is compact for n ≥ 1
    have hC_compact : ∀ n, 1 ≤ n → IsCompact (C n) := by
      intro n hn
      exact isCompact_Icc.of_isClosed_subset (hC_closed n) (hC_bounded n hn)
    -- Key backward implication: C (n+1) conditions imply C n conditions
    -- More precisely: if 1 - 1/(n+1) ≤ f (n+1) a ≤ 1, then 1 - 1/n ≤ f n a ≤ 1
    -- This shows C_n = S_n where S_n = {a | 1 - 1/n ≤ f n a ≤ 1}
    have hbackward : ∀ n : ℕ, 0 < n → ∀ a : NNReal,
        1 - 1 / (↑(n + 1) : ℝ) ≤ f (n + 1) a → f (n + 1) a ≤ 1 →
        1 - 1 / (↑n : ℝ) ≤ f n a ∧ f n a ≤ 1 := by
      intro n hn a hlower hupper
      constructor
      · -- 1 - 1/n ≤ f n a: by contrapositive
        -- If f n a < 1 - 1/n, then f n a * (f n a + 1/n) ≤ (1-1/n) * 1 = 1 - 1/n < 1 - 1/(n+1)
        -- contradicting 1 - 1/(n+1) ≤ f (n+1) a
        by_contra h; push_neg at h
        have h1 : f n a + 1 / (↑n : ℝ) < 1 := by linarith
        have h2 : f (n + 1) a < 1 - 1 / (↑n : ℝ) := by
          rw [h₁]
          have := hfnn n (by omega) a
          nlinarith
        have h3 : 1 / (↑(n + 1) : ℝ) < 1 / (↑n : ℝ) := by
          apply div_lt_div_of_pos_left one_pos (Nat.cast_pos.mpr hn)
          exact_mod_cast show (n : ℕ) < n + 1 by omega
        linarith
      · -- f n a ≤ 1: if f n a > 1, then f (n+1) a = f n a * (f n a + 1/n) > 1 * (1 + 1/n) > 1
        -- contradicting f (n+1) a ≤ 1
        by_contra h; push_neg at h
        have : f (n + 1) a > 1 := by
          rw [h₁]
          have h1 : (0 : ℝ) < 1 / ↑n := by positivity
          nlinarith [hfnn n (by omega) a]
        linarith
    -- C n is nonempty for all n ≥ 1
    -- Proof: By IVT, f n achieves the value (1 - 1/(2n)) (or any value in (1-1/n, 1))
    -- at some point a_n. Then a_n ∈ S_n = C_n.
    -- We need: f n 0 = 0 ≤ 1 - 1/n and there exists M with f n M ≥ 1.
    have hC_nonempty : ∀ n, 1 ≤ n → (C n).Nonempty := by
      intro n hn
      -- It suffices to find a with 1 - 1/n ≤ f n a ≤ 1 (then by hbackward, a ∈ C n)
      -- But actually we need a ∈ C n, which requires conditions for ALL k ≤ n.
      -- We use: C_n = S_n (by repeated application of hbackward)
      suffices ∃ a : NNReal, 1 - 1 / (↑n : ℝ) ≤ f n a ∧ f n a ≤ 1 by
        obtain ⟨a, ha_lower, ha_upper⟩ := this
        refine ⟨a, ?_⟩
        -- Show a ∈ C n, i.e., for all k with 1 ≤ k ≤ n: 1 - 1/k ≤ f k a ≤ 1
        -- By induction downward from n using hbackward
        intro k hk hkn
        -- By induction from n down to k
        induction n with
        | zero => omega
        | succ m ih =>
          by_cases hkm : k ≤ m
          · exact ih (by omega) (hbackward m (by omega) a ha_lower ha_upper).1
              (hbackward m (by omega) a ha_lower ha_upper).2 hkm
          · push_neg at hkm
            have : k = m + 1 := by omega
            rw [this]; exact ⟨ha_lower, ha_upper⟩
      -- Now find a with 1 - 1/n ≤ f n a ≤ 1
      -- By IVT: f n 0 = 0 and there exists M with f n M ≥ 1
      -- First, find M with f n M ≥ 1
      have hM : ∃ M : NNReal, 1 ≤ f n M := by
        -- f 1 1 = 1, so for n = 1, M = 1 works
        -- For n > 1, f n is continuous, strictly increasing with f n 0 = 0
        -- and f n → ∞, so there exists M with f n M ≥ 1
        -- We can use f n 1 ≥ ... or just use IVT
        -- Actually, let's show f 1 ⟨1, le_refl _⟩ = 1 for the base case
        -- and then f n 1 ≥ 1 for all n (by induction)
        -- Hmm, f 2 1 = 1 * (1 + 1) = 2 > 1. f 3 1 = 2 * (2 + 1/2) = 5 > 1.
        -- In general f n 1 ≥ 1 for all n ≥ 1 (by induction, since f (n+1) 1 = f n 1 * (f n 1 + 1/n) ≥ 1 * 2 = 2)
        -- Wait, not quite. Let me just use IVT with a large enough M.
        -- Actually, f n is strictly monotone and f n 0 = 0, f n 1 = ... ≥ 1 (checkable).
        -- Let's just find M = 1 works: f 1 1 = 1.
        -- f 2 1 = 1 * (1 + 1) = 2 > 1.
        -- f (n+1) 1 = f n 1 * (f n 1 + 1/n) ≥ 1 * (1 + 0) = 1 if f n 1 ≥ 1. By induction.
        use 1
        induction n with
        | zero => omega
        | succ m ih_m =>
          cases m with
          | zero => rw [h₀]; simp
          | succ m =>
            rw [h₁]
            have hm : 1 ≤ f (m + 1) 1 := ih_m (by omega)
            have : (0 : ℝ) < 1 / (↑(m + 1) : ℝ) := by positivity
            nlinarith
      obtain ⟨M, hM⟩ := hM
      -- By IVT between 0 and M: f n 0 = 0 ≤ 1 - 1/n ≤ 1 ≤ f n M
      have h0 : f n 0 ≤ 1 - 1 / (↑n : ℝ) := by
        rw [hf0 n (by omega)]
        have : 1 / (↑n : ℝ) ≤ 1 := by
          rw [div_le_one (Nat.cast_pos.mpr (by omega))]; exact_mod_cast hn
        linarith
      -- Find a with f n a = 1 - 1/n (if 1 - 1/n ≥ 0, which it is for n ≥ 1)
      -- Actually, I need a with f n a in [1-1/n, 1].
      -- By IVT, there exist a_lo with f n a_lo = 1 - 1/n (using f n 0 = 0 ≤ 1-1/n and f n M ≥ 1 > 1-1/n)
      have htarget_le : 1 - 1 / (↑n : ℝ) ≤ 1 := by linarith [show (0 : ℝ) < 1 / ↑n from by positivity]
      obtain ⟨a, ha_eq⟩ := intermediate_value_univ₂ (hcont n (by omega)) continuous_const
        h0 (le_trans htarget_le hM)
      exact ⟨a, le_of_eq ha_eq.symm, by rw [ha_eq]; exact htarget_le⟩
    -- Apply Cantor's intersection theorem on the sequence C(n+1)
    have hinter : (⋂ n, C (n + 1)).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        (fun n => C (n + 1))
      · intro i; exact hC_mono (i + 1)
      · intro i; exact hC_nonempty (i + 1) (by omega)
      · exact hC_compact 1 le_rfl
      · intro i; exact hC_closed (i + 1)
    obtain ⟨a, ha_mem⟩ := hinter
    rw [Set.mem_iInter] at ha_mem
    -- a satisfies: for all n ≥ 1, 1 - 1/n ≤ f n a ≤ 1
    have ha_weak : ∀ n : ℕ, 0 < n → 1 - 1 / (↑n : ℝ) ≤ f n a ∧ f n a ≤ 1 := by
      intro n hn
      -- a ∈ C (n + 1), and n ≤ n + 1, so condition holds for k = n
      have hmem : a ∈ C (n + 1) := by
        -- a ∈ C (m + 1) for all m, so in particular for m = n
        exact ha_mem n
      exact hmem n hn (Nat.le_succ n)
    -- Upgrade to strict: f n a < 1
    have ha_strict_upper : ∀ n : ℕ, 0 < n → f n a < 1 := by
      intro n hn
      have h_le := (ha_weak n hn).2
      by_contra h_eq; push_neg at h_eq
      have heq : f n a = 1 := le_antisymm h_le h_eq
      have h_next := (ha_weak (n + 1) (by omega)).2
      rw [h₁, heq] at h_next
      have : (1 : ℝ) * (1 + 1 / ↑n) ≤ 1 := h_next
      linarith [show (0 : ℝ) < 1 / ↑n from by positivity]
    -- Upgrade to strict: 1 - 1/n < f n a
    have ha_strict_lower : ∀ n : ℕ, 0 < n → 1 - 1 / (↑n : ℝ) < f n a := by
      intro n hn
      have h_le := (ha_weak n hn).1
      by_contra h_eq; push_neg at h_eq
      have hfn : f n a = 1 - 1 / (↑n : ℝ) := le_antisymm h_eq h_le
      have h_next_lower := (ha_weak (n + 1) (by omega)).1
      rw [h₁, hfn] at h_next_lower
      have hsimpl : (1 - 1 / (↑n : ℝ)) * (1 - 1 / ↑n + 1 / ↑n) = 1 - 1 / ↑n := by ring
      rw [hsimpl] at h_next_lower
      -- Need: 1 - 1/(n+1) ≤ 1 - 1/n, but 1/(n+1) < 1/n
      have hlt : 1 / (↑(n + 1) : ℝ) < 1 / (↑n : ℝ) := by
        apply div_lt_div_of_pos_left one_pos (Nat.cast_pos.mpr hn)
        exact_mod_cast show (n : ℕ) < n + 1 by omega
      linarith
    -- Now derive the original strict conditions
    refine ⟨a, fun n hn => ⟨?_, ?_, ?_⟩⟩
    · -- 0 < f n a
      have h1 := ha_strict_lower n hn
      have h2 : (0 : ℝ) ≤ 1 - 1 / (↑n : ℝ) := by
        have : 1 / (↑n : ℝ) ≤ 1 := by
          rw [div_le_one (Nat.cast_pos.mpr hn)]; exact_mod_cast hn
        linarith
      linarith
    · -- f n a < f (n+1) a
      rw [h₁]
      have hpos : 0 < f n a := by
        have := ha_strict_lower n hn
        have : (0 : ℝ) ≤ 1 - 1 / (↑n : ℝ) := by
          have : 1 / (↑n : ℝ) ≤ 1 := by
            rw [div_le_one (Nat.cast_pos.mpr hn)]; exact_mod_cast hn
          linarith
        linarith
      have h1 : 1 < f n a + 1 / (↑n : ℝ) := by linarith [ha_strict_lower n hn]
      nlinarith
    · -- f (n+1) a < 1
      exact ha_strict_upper (n + 1) (by omega)
  obtain ⟨a, ha⟩ := hexist
  exact ⟨a, ha, fun b hb => huniq b a hb ha⟩
