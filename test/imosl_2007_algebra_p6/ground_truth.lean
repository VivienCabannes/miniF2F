import Mathlib

open BigOperators Real Nat Topology Rat Finset

set_option maxHeartbeats 6400000

theorem imosl_2007_algebra_p6
  (a : ℕ → NNReal)
  (h₀ : ∑ x ∈ Finset.range 100, ((a (x + 1))^2) = 1) :
  ∑ x ∈ Finset.range 99, ((a (x + 1))^2 * a (x + 2)) + (a 100)^2 * a 1 < 12 / 25 := by
  -- b is the 0-indexed cast to ℝ
  let b : ℕ → ℝ := fun k => (a (k + 1) : ℝ)
  have hb_nn : ∀ k, 0 ≤ b k := fun k => (a (k + 1)).coe_nonneg
  have hb_sq : ∑ k ∈ range 100, b k ^ 2 = 1 := by
    have : (↑(∑ x ∈ range 100, ((a (x + 1))^2)) : ℝ) = (1 : ℝ) := by exact_mod_cast h₀
    simp only [NNReal.coe_sum, NNReal.coe_pow] at this
    exact this
  -- LHS in ℝ
  let S : ℝ := ∑ x ∈ range 99, b x ^ 2 * b (x + 1) + b 99 ^ 2 * b 0
  have hS_nn : 0 ≤ S := by
    show 0 ≤ ∑ x ∈ range 99, b x ^ 2 * b (x + 1) + b 99 ^ 2 * b 0
    apply add_nonneg
    · exact sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hb_nn _)
    · exact mul_nonneg (sq_nonneg _) (hb_nn _)
  -- The NNReal LHS cast to ℝ = S
  have hLHS_eq : (↑(∑ x ∈ range 99, ((a (x + 1))^2 * a (x + 2)) + (a 100)^2 * a 1) : ℝ) = S := by
    show _ = ∑ x ∈ range 99, b x ^ 2 * b (x + 1) + b 99 ^ 2 * b 0
    simp only [NNReal.coe_add, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_pow]
    rfl
  -- 12/25 in NNReal cast to ℝ
  have h12_eq : ((12 / 25 : NNReal) : ℝ) = 12 / 25 := by norm_num
  -- Suffices to show S < 12/25 in ℝ
  rw [← NNReal.coe_lt_coe, hLHS_eq, h12_eq]
  -- Goal: S < 12/25 in ℝ

  -- Show 9*S^2 ≤ 2
  suffices hkey : 9 * S ^ 2 ≤ 2 by
    show S < 12 / 25
    by_contra hc; push_neg at hc
    have h1 : (12 / 25 : ℝ) ^ 2 ≤ S ^ 2 := sq_le_sq' (by linarith) hc
    have : 9 * (12 / 25 : ℝ) ^ 2 ≤ 2 := by nlinarith
    norm_num at this

  -- c(k) = b(k % 100) for cyclic indexing
  let c : ℕ → ℝ := fun k => b (k % 100)
  have hc_nn : ∀ k, 0 ≤ c k := fun k => hb_nn _
  have hc_eq : ∀ k, k < 100 → c k = b k := fun k hk => by show b (k % 100) = b k; rw [Nat.mod_eq_of_lt hk]
  have hc_sq : ∑ k ∈ range 100, c k ^ 2 = 1 := by
    show ∑ k ∈ range 100, b (k % 100) ^ 2 = 1
    have : ∀ k ∈ range 100, b (k % 100) ^ 2 = b k ^ 2 := by
      intro k hk; rw [Nat.mod_eq_of_lt (mem_range.mp hk)]
    rw [Finset.sum_congr rfl this]; exact hb_sq
  have hc_mod : ∀ k, c (k % 100) = c k := by
    intro k; show b (k % 100 % 100) = b (k % 100); rw [Nat.mod_mod]

  -- S = ∑ c(k)^2 * c(k+1) over range 100
  have hS_eq : S = ∑ k ∈ range 100, c k ^ 2 * c (k + 1) := by
    show ∑ x ∈ range 99, b x ^ 2 * b (x + 1) + b 99 ^ 2 * b 0 =
      ∑ k ∈ range 100, b (k % 100) ^ 2 * b ((k + 1) % 100)
    -- RHS = ∑_{k=0}^{98} b(k)^2*b(k+1) + b(99)^2*b(0), which is S
    symm
    rw [Finset.sum_range_succ]; norm_num
    -- Goal: ∑ k ∈ range 99, b(k%100)^2 * b((k+1)%100) = ∑ x ∈ range 99, b(x)^2*b(x+1)
    apply Finset.sum_congr rfl; intro k hk; rw [mem_range] at hk
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

  -- Cyclic shift lemma: ∑ g((k+m) % 100) = ∑ g(k) over range 100
  have cyclic_sum_shift : ∀ (g : ℕ → ℝ) (m : ℕ),
      ∑ k ∈ range 100, g ((k + m) % 100) = ∑ k ∈ range 100, g k := by
    intro g m
    -- Use Finset.sum_nbij' with forward map k ↦ (k+m)%100 and inverse j ↦ (j+100-m%100)%100
    let fwd := fun k => (k + m) % 100
    let bwd := fun j => (j + (100 - m % 100)) % 100
    apply Finset.sum_nbij' fwd bwd
    · intro k _; exact mem_range.mpr (Nat.mod_lt _ (by norm_num))
    · intro j _; exact mem_range.mpr (Nat.mod_lt _ (by norm_num))
    · -- left inverse: bwd (fwd k) = k for k ∈ range 100
      intro k hk; rw [mem_range] at hk
      show ((k + m) % 100 + (100 - m % 100)) % 100 = k
      omega
    · -- right inverse: fwd (bwd j) = j for j ∈ range 100
      intro j hj; rw [mem_range] at hj
      show ((j + (100 - m % 100)) % 100 + m) % 100 = j
      omega
    · intro k _; rfl

  -- Shift identity: ∑ c(k+99)^2 * c(k) = S
  have shift_identity : ∑ k ∈ range 100, c (k + 99) ^ 2 * c k = S := by
    rw [hS_eq]
    show ∑ k ∈ range 100, b ((k + 99) % 100) ^ 2 * b (k % 100) =
      ∑ k ∈ range 100, b (k % 100) ^ 2 * b ((k + 1) % 100)
    rw [← cyclic_sum_shift (fun j => b (j % 100) ^ 2 * b ((j + 1) % 100)) 99]
    apply sum_congr rfl; intro k hk
    simp only [mem_range] at hk
    show b ((k + 99) % 100) ^ 2 * b (k % 100) =
      b (((k + 99) % 100) % 100) ^ 2 * b (((k + 99) % 100 + 1) % 100)
    congr 1
    · congr 1; rw [Nat.mod_mod]
    · congr 1
      have hk' : k < 100 := hk
      -- Need: ((k + 99) % 100 + 1) % 100 = k % 100
      -- k < 100, so k % 100 = k
      rw [Nat.mod_eq_of_lt hk']
      -- Case split on k
      by_cases hk0 : k = 0
      · subst hk0; norm_num
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have : (k + 99) % 100 = k - 1 := by omega
        rw [this]; omega

  -- f(k) = c(k+99)^2 + 2*c(k)*c(k+1)
  let f : ℕ → ℝ := fun k => c (k + 99) ^ 2 + 2 * c k * c (k + 1)

  -- 3S = ∑ c(k) * f(k)
  have three_S : 3 * S = ∑ k ∈ range 100, c k * f k := by
    show 3 * S = ∑ k ∈ range 100, c k * (c (k + 99) ^ 2 + 2 * c k * c (k + 1))
    have h1 : ∑ k ∈ range 100, c k * c (k + 99) ^ 2 = S := by
      rw [show (∑ k ∈ range 100, c k * c (k + 99) ^ 2) =
        ∑ k ∈ range 100, c (k + 99) ^ 2 * c k from by congr 1; ext k; ring]
      exact shift_identity
    have h2 : ∑ k ∈ range 100, (2 * c k ^ 2 * c (k + 1)) = 2 * S := by
      rw [hS_eq, Finset.mul_sum]; congr 1; ext k; ring
    calc 3 * S = S + 2 * S := by ring
      _ = _ + _ := by rw [h1, h2]
      _ = ∑ k ∈ range 100, (c k * c (k + 99) ^ 2 + 2 * c k ^ 2 * c (k + 1)) :=
          (Finset.sum_add_distrib).symm
      _ = ∑ k ∈ range 100, c k * (c (k + 99) ^ 2 + 2 * c k * c (k + 1)) := by
          congr 1; ext k; ring

  -- Cauchy-Schwarz: 9S^2 ≤ ∑ f(k)^2
  have hCS : 9 * S ^ 2 ≤ ∑ k ∈ range 100, f k ^ 2 := by
    have hcs := sum_mul_sq_le_sq_mul_sq (range 100) c f
    rw [hc_sq, one_mul] at hcs
    calc 9 * S ^ 2 = (3 * S) ^ 2 := by ring
      _ = (∑ k ∈ range 100, c k * f k) ^ 2 := by rw [three_S]
      _ ≤ ∑ k ∈ range 100, f k ^ 2 := hcs

  -- ∑ f(k)^2 ≤ 2
  suffices hf_bound : ∑ k ∈ range 100, f k ^ 2 ≤ 2 by linarith

  -- Per-term AM-GM bound
  have hf_bt : ∀ k, f k ^ 2 ≤
      (c (k + 99) ^ 4 + 2 * c (k + 99) ^ 2 * c k ^ 2 + 2 * c (k + 99) ^ 2 * c (k + 1) ^ 2)
      + 4 * c k ^ 2 * c (k + 1) ^ 2 := by
    intro k
    show (c (k + 99) ^ 2 + 2 * c k * c (k + 1)) ^ 2 ≤ _
    nlinarith [sq_nonneg (c (k + 99) * (c k - c (k + 1))),
               hc_nn (k + 99), hc_nn k, hc_nn (k + 1),
               mul_nonneg (hc_nn k) (hc_nn (k + 1))]

  calc ∑ k ∈ range 100, f k ^ 2
      ≤ ∑ k ∈ range 100, ((c (k + 99) ^ 4 + 2 * c (k + 99) ^ 2 * c k ^ 2 +
            2 * c (k + 99) ^ 2 * c (k + 1) ^ 2) + 4 * c k ^ 2 * c (k + 1) ^ 2) :=
        Finset.sum_le_sum (fun k _ => hf_bt k)
    _ = ∑ k ∈ range 100, (c (k + 99) ^ 4 + 2 * c (k + 99) ^ 2 * c k ^ 2 +
            2 * c (k + 99) ^ 2 * c (k + 1) ^ 2) +
        ∑ k ∈ range 100, (4 * c k ^ 2 * c (k + 1) ^ 2) :=
        Finset.sum_add_distrib
    _ ≤ 1 + 1 := by
        apply _root_.add_le_add
        · -- Part A: ∑(c(k+99)⁴ + 2c(k+99)²c_k² + 2c(k+99)²c_{k+1}²) ≤ 1
          -- T(d) = ∑_k c(k)²·c((k+d)%100)², Part A = T(0)+2T(1)+2T(2) ≤ ∑T(d) = (∑c²)² = 1
          let T : ℕ → ℝ := fun d => ∑ k ∈ range 100, c k ^ 2 * c ((k + d) % 100) ^ 2
          have hT_nn : ∀ d, 0 ≤ T d :=
            fun d => sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
          -- Split into three sums
          have h_split : ∑ k ∈ range 100, (c (k + 99) ^ 4 + 2 * c (k + 99) ^ 2 * c k ^ 2 +
              2 * c (k + 99) ^ 2 * c (k + 1) ^ 2) =
            ∑ k ∈ range 100, c (k + 99) ^ 4 +
            2 * ∑ k ∈ range 100, c (k + 99) ^ 2 * c k ^ 2 +
            2 * ∑ k ∈ range 100, c (k + 99) ^ 2 * c (k + 1) ^ 2 := by
            have h1 : ∀ k, c (k + 99) ^ 4 + 2 * c (k + 99) ^ 2 * c k ^ 2 +
                2 * c (k + 99) ^ 2 * c (k + 1) ^ 2 =
                c (k + 99) ^ 4 + (2 * (c (k + 99) ^ 2 * c k ^ 2) +
                2 * (c (k + 99) ^ 2 * c (k + 1) ^ 2)) := fun k => by ring
            simp_rw [h1]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            ring
          -- ∑ c(k+99)^4 = T(0)
          have hS0 : ∑ k ∈ range 100, c (k + 99) ^ 4 = T 0 := by
            show _ = ∑ k ∈ range 100, c k ^ 2 * c ((k + 0) % 100) ^ 2
            have h := cyclic_sum_shift (fun j => c j ^ 4) 99
            simp only [hc_mod] at h
            rw [h]
            apply sum_congr rfl; intro k hk
            have hk' := mem_range.mp hk
            have hmod : (k + 0) % 100 = k := by omega
            rw [hmod]; ring
          -- ∑ c(k+99)^2 * c(k)^2 = T(1)
          have hS1 : ∑ k ∈ range 100, c (k + 99) ^ 2 * c k ^ 2 = T 1 := by
            show _ = ∑ k ∈ range 100, c k ^ 2 * c ((k + 1) % 100) ^ 2
            rw [← cyclic_sum_shift (fun j => c j ^ 2 * c ((j + 1) % 100) ^ 2) 99]
            apply sum_congr rfl; intro k hk
            have hk' := mem_range.mp hk
            have hmod : ((k + 99) % 100 + 1) % 100 = k := by omega
            rw [hc_mod (k + 99), hmod]
          -- ∑ c(k+99)^2 * c(k+1)^2 = T(2)
          have hS2 : ∑ k ∈ range 100, c (k + 99) ^ 2 * c (k + 1) ^ 2 = T 2 := by
            show _ = ∑ k ∈ range 100, c k ^ 2 * c ((k + 2) % 100) ^ 2
            rw [← cyclic_sum_shift (fun j => c j ^ 2 * c ((j + 2) % 100) ^ 2) 99]
            apply sum_congr rfl; intro k hk
            have hk' := mem_range.mp hk
            have hmod : ((k + 99) % 100 + 2) % 100 = (k + 1) % 100 := by omega
            rw [hc_mod (k + 99), hmod, hc_mod (k + 1)]
          rw [h_split, hS0, hS1, hS2]
          -- T(99) = T(1)
          have hT99 : T 99 = T 1 := by
            show ∑ k ∈ range 100, c k ^ 2 * c ((k + 99) % 100) ^ 2 =
                 ∑ k ∈ range 100, c k ^ 2 * c ((k + 1) % 100) ^ 2
            rw [← cyclic_sum_shift (fun j => c j ^ 2 * c ((j + 99) % 100) ^ 2) 1]
            apply sum_congr rfl; intro k hk
            have hk' := mem_range.mp hk
            have hmod : ((k + 1) % 100 + 99) % 100 = k := by omega
            rw [hc_mod (k + 1), hmod]; ring
          -- T(98) = T(2)
          have hT98 : T 98 = T 2 := by
            show ∑ k ∈ range 100, c k ^ 2 * c ((k + 98) % 100) ^ 2 =
                 ∑ k ∈ range 100, c k ^ 2 * c ((k + 2) % 100) ^ 2
            rw [← cyclic_sum_shift (fun j => c j ^ 2 * c ((j + 98) % 100) ^ 2) 2]
            apply sum_congr rfl; intro k hk
            have hk' := mem_range.mp hk
            have hmod : ((k + 2) % 100 + 98) % 100 = k := by omega
            rw [hc_mod (k + 2), hmod]; ring
          -- ∑ T(d) = 1
          have h1_eq : ∑ d ∈ range 100, T d = 1 := by
            have hsq : (∑ k ∈ range 100, c k ^ 2) ^ 2 = ∑ d ∈ range 100, T d := by
              rw [sq, Finset.sum_mul, Finset.sum_comm]
              apply sum_congr rfl; intro k _
              -- Goal: c(k)² * ∑ c(j)² = ∑_d c(k)² * c((k+d)%100)²
              conv_rhs => rw [← Finset.mul_sum]
              congr 1
              -- Goal: ∑ c(j)² = ∑_d c((k+d)%100)²
              have hshift := (cyclic_sum_shift (fun j => c j ^ 2) k).symm
              rw [hshift]
              apply sum_congr rfl; intro d _
              congr 1; congr 1; omega
            rw [hc_sq, one_pow] at hsq; exact hsq.symm
          -- T(0) + 2T(1) + 2T(2) ≤ ∑ T(d) = 1
          rw [← h1_eq]
          suffices hfin : ∑ d ∈ ({0, 1, 2, 98, 99} : Finset ℕ), T d =
              T 0 + T 1 + T 2 + T 98 + T 99 by
            linarith [sum_le_sum_of_subset_of_nonneg
              (show ({0, 1, 2, 98, 99} : Finset ℕ) ⊆ range 100 from by decide)
              (fun d _ _ => hT_nn d)]
          have h01 : (0 : ℕ) ∉ ({1, 2, 98, 99} : Finset ℕ) := by decide
          have h12 : (1 : ℕ) ∉ ({2, 98, 99} : Finset ℕ) := by decide
          have h23 : (2 : ℕ) ∉ ({98, 99} : Finset ℕ) := by decide
          have h34 : (98 : ℕ) ∉ ({99} : Finset ℕ) := by decide
          rw [show ({0, 1, 2, 98, 99} : Finset ℕ) =
            insert 0 (insert 1 (insert 2 (insert 98 {99}))) from rfl]
          rw [sum_insert h01, sum_insert h12, sum_insert h23, sum_insert h34, sum_singleton]
          ring
        · -- Part B: 4∑c_k²c_{k+1}² ≤ 1
          -- Factor out 4, then show ∑c(k)²c(k+1)² ≤ E·O ≤ 1/4
          have h_pull4 : ∑ k ∈ range 100, (4 * c k ^ 2 * c (k + 1) ^ 2) =
              4 * ∑ k ∈ range 100, (c k ^ 2 * c (k + 1) ^ 2) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
          rw [h_pull4]
          -- Even/odd sums
          set E := ∑ i ∈ range 50, c (2 * i) ^ 2
          set O := ∑ i ∈ range 50, c (2 * i + 1) ^ 2
          have hE_nn : 0 ≤ E := sum_nonneg fun i _ => sq_nonneg _
          have hO_nn : 0 ≤ O := sum_nonneg fun i _ => sq_nonneg _
          -- E + O = 1
          have hEO : E + O = 1 := by
            rw [← hc_sq]
            have h100 : (100 : ℕ) = 2 * 50 := by norm_num
            rw [h100]
            -- Split range (2*50) into even and odd
            have : ∀ (n : ℕ) (f : ℕ → ℝ), ∑ k ∈ range (2 * n), f k =
                ∑ i ∈ range n, f (2 * i) + ∑ i ∈ range n, f (2 * i + 1) := by
              intro n f; induction n with
              | zero => simp
              | succ n ih =>
                rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
                    show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
                rw [Finset.sum_range_succ, show 2 * n + 1 = (2 * n) + 1 from by ring,
                    Finset.sum_range_succ, ih]
                rw [Finset.sum_range_succ (fun i => f (2 * i)),
                    Finset.sum_range_succ (fun i => f (2 * i + 1))]
                ring
            exact (this 50 (fun k => c k ^ 2)).symm
          -- Q ≤ E * O via subset argument
          have hQ_le : ∑ k ∈ range 100, (c k ^ 2 * c (k + 1) ^ 2) ≤ E * O := by
            have h100 : (100 : ℕ) = 2 * 50 := by norm_num
            have even_odd_split : ∀ (n : ℕ) (f : ℕ → ℝ), ∑ k ∈ range (2 * n), f k =
                ∑ i ∈ range n, f (2 * i) + ∑ i ∈ range n, f (2 * i + 1) := by
              intro n f; induction n with
              | zero => simp
              | succ n ih =>
                rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
                    show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
                rw [Finset.sum_range_succ, show 2 * n + 1 = (2 * n) + 1 from by ring,
                    Finset.sum_range_succ, ih]
                rw [Finset.sum_range_succ (fun i => f (2 * i)),
                    Finset.sum_range_succ (fun i => f (2 * i + 1))]
                ring
            rw [h100, even_odd_split, Finset.sum_mul_sum]
            -- Rewrite c(2i+1+1) = c(2*((i+1)%50)) using cyclicity
            have hodd_rw : ∀ i ∈ range 50,
                c (2 * i + 1) ^ 2 * c (2 * i + 1 + 1) ^ 2 =
                c (2 * ((i + 1) % 50)) ^ 2 * c (2 * i + 1) ^ 2 := by
              intro i hi; rw [mem_range] at hi
              have : c (2 * i + 1 + 1) = c (2 * ((i + 1) % 50)) := by
                show c (2 * i + 2) = c (2 * ((i + 1) % 50))
                by_cases hi49 : i = 49
                · subst hi49; norm_num; exact (hc_mod 100).symm
                · have : (i + 1) % 50 = i + 1 := Nat.mod_eq_of_lt (by omega)
                  rw [this]; ring_nf
              rw [this]; ring
            rw [Finset.sum_congr rfl hodd_rw]
            set g := fun p : ℕ × ℕ => c (2 * p.1) ^ 2 * c (2 * p.2 + 1) ^ 2
            have hrhs_eq : ∑ i ∈ range 50, ∑ j ∈ range 50,
                c (2 * i) ^ 2 * c (2 * j + 1) ^ 2 =
                ∑ p ∈ range 50 ×ˢ range 50, g p := by
              rw [← Finset.sum_product']
            have hfirst_eq : ∑ i ∈ range 50, c (2 * i) ^ 2 * c (2 * i + 1) ^ 2 =
                ∑ p ∈ (range 50).image (fun i => (i, i)), g p := by
              rw [Finset.sum_image]; intro a _ b _ hab; exact (Prod.mk.inj hab).1
            have hsecond_eq : ∑ i ∈ range 50,
                c (2 * ((i + 1) % 50)) ^ 2 * c (2 * i + 1) ^ 2 =
                ∑ p ∈ (range 50).image (fun i => ((i + 1) % 50, i)), g p := by
              rw [Finset.sum_image]; intro a _ b _ hab; exact (Prod.mk.inj hab).2
            rw [hfirst_eq, hsecond_eq, hrhs_eq]
            -- S1 and S2 are disjoint
            have hS_disj : Disjoint
                ((range 50).image (fun i => (i, i)))
                ((range 50).image (fun i => ((i + 1) % 50, i))) := by
              rw [Finset.disjoint_left]
              intro p hp1 hp2
              rw [Finset.mem_image] at hp1 hp2
              obtain ⟨a, _, rfl⟩ := hp1
              obtain ⟨b, hb, heq⟩ := hp2
              rw [mem_range] at hb
              have h1 := congr_arg Prod.fst heq
              have h2 := congr_arg Prod.snd heq
              simp only at h1 h2
              subst h2; omega
            -- S1 ∪ S2 ⊆ range 50 ×ˢ range 50
            have hS_sub : (range 50).image (fun i => (i, i)) ∪
                          (range 50).image (fun i => ((i + 1) % 50, i)) ⊆
                          range 50 ×ˢ range 50 := by
              intro p hp
              rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hp
              rw [mem_product, mem_range, mem_range]
              rcases hp with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
              · rw [mem_range] at ha; exact ⟨ha, ha⟩
              · rw [mem_range] at hb; exact ⟨Nat.mod_lt _ (by norm_num), hb⟩
            rw [← Finset.sum_union hS_disj]
            exact Finset.sum_le_sum_of_subset_of_nonneg hS_sub
              (fun p _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          -- 4EO ≤ 1 by AM-GM
          have h4EO : 4 * (E * O) ≤ 1 := by
            nlinarith [sq_nonneg (E - O), hEO]
          linarith [hQ_le, h4EO]
    _ = 2 := by ring
