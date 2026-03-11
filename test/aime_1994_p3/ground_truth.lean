import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1994_p3
  (f : ℤ → ℤ)
  (h0 : f x + f (x-1) = x^2)
  (h1 : f 19 = 94):
  f (94) % 1000 = 561 := by
  have h2 : f 18 = 267 := by
    have h2₁ := h0 19
    have h2₂ : f 19 + f 18 = 361 := by
      norm_num at h2₁ ⊢
      <;> linarith
    have h2₃ : f 18 = 267 := by
      linarith
    exact h2₃
  
  have h3 : f 17 = 57 := by
    have h3₁ : f 18 + f 17 = 324 := by
      have h3₂ := h0 18
      norm_num at h3₂ ⊢
      <;> linarith
    have h3₃ : f 17 = 57 := by
      linarith
    exact h3₃
  
  have h4 : f 16 = 232 := by
    have h4₁ : f 17 + f 16 = 289 := by
      have h4₂ := h0 17
      norm_num at h4₂ ⊢
      <;> linarith
    have h4₃ : f 16 = 232 := by
      linarith
    exact h4₃
  
  have h5 : f 15 = 24 := by
    have h5₁ : f 16 + f 15 = 256 := by
      have h5₂ := h0 16
      norm_num at h5₂ ⊢
      <;> linarith
    have h5₃ : f 15 = 24 := by
      linarith
    exact h5₃
  
  have h6 : f 14 = 201 := by
    have h6₁ : f 15 + f 14 = 225 := by
      have h6₂ := h0 15
      norm_num at h6₂ ⊢
      <;> linarith
    have h6₃ : f 14 = 201 := by
      linarith
    exact h6₃
  
  have h7 : f 13 = (-5) := by
    have h7₁ : f 14 + f 13 = 196 := by
      have h7₂ := h0 14
      norm_num at h7₂ ⊢
      <;> linarith
    have h7₃ : f 13 = -5 := by
      linarith
    exact h7₃
  
  have h8 : f 12 = 174 := by
    have h8₁ : f 13 + f 12 = 169 := by
      have h8₂ := h0 13
      norm_num at h8₂ ⊢
      <;> linarith
    have h8₃ : f 12 = 174 := by
      linarith
    exact h8₃
  
  have h9 : f 11 = (-30) := by
    have h9₁ : f 12 + f 11 = 144 := by
      have h9₂ := h0 12
      norm_num at h9₂ ⊢
      <;> linarith
    have h9₃ : f 11 = -30 := by
      linarith
    exact h9₃
  
  have h10 : f 10 = 151 := by
    have h10₁ : f 11 + f 10 = 121 := by
      have h10₂ := h0 11
      norm_num at h10₂ ⊢
      <;> linarith
    have h10₃ : f 10 = 151 := by
      linarith
    exact h10₃
  
  have h11 : f 9 = (-51) := by
    have h11₁ : f 10 + f 9 = 100 := by
      have h11₂ := h0 10
      norm_num at h11₂ ⊢
      <;> linarith
    have h11₃ : f 9 = -51 := by
      linarith
    exact h11₃
  
  have h12 : f 8 = 132 := by
    have h12₁ : f 9 + f 8 = 81 := by
      have h12₂ := h0 9
      norm_num at h12₂ ⊢
      <;> linarith
    have h12₃ : f 8 = 132 := by
      linarith
    exact h12₃
  
  have h13 : f 7 = (-68) := by
    have h13₁ : f 8 + f 7 = 64 := by
      have h13₂ := h0 8
      norm_num at h13₂ ⊢
      <;> linarith
    have h13₃ : f 7 = -68 := by
      linarith
    exact h13₃
  
  have h14 : f 6 = 117 := by
    have h14₁ : f 7 + f 6 = 49 := by
      have h14₂ := h0 7
      norm_num at h14₂ ⊢
      <;> linarith
    have h14₃ : f 6 = 117 := by
      linarith
    exact h14₃
  
  have h15 : f 5 = (-81) := by
    have h15₁ : f 6 + f 5 = 36 := by
      have h15₂ := h0 6
      norm_num at h15₂ ⊢
      <;> linarith
    have h15₃ : f 5 = -81 := by
      linarith
    exact h15₃
  
  have h16 : f 4 = 106 := by
    have h16₁ : f 5 + f 4 = 25 := by
      have h16₂ := h0 5
      norm_num at h16₂ ⊢
      <;> linarith
    have h16₃ : f 4 = 106 := by
      linarith
    exact h16₃
  
  have h17 : f 3 = (-90) := by
    have h17₁ : f 4 + f 3 = 16 := by
      have h17₂ := h0 4
      norm_num at h17₂ ⊢
      <;> linarith
    have h17₃ : f 3 = -90 := by
      linarith
    exact h17₃
  
  have h18 : f 2 = 99 := by
    have h18₁ : f 3 + f 2 = 9 := by
      have h18₂ := h0 3
      norm_num at h18₂ ⊢
      <;> linarith
    have h18₃ : f 2 = 99 := by
      linarith
    exact h18₃
  
  have h19 : f 1 = (-95) := by
    have h19₁ : f 2 + f 1 = 4 := by
      have h19₂ := h0 2
      norm_num at h19₂ ⊢
      <;> linarith
    have h19₃ : f 1 = -95 := by
      linarith
    exact h19₃
  
  have h20 : f 0 = 96 := by
    have h20₁ : f 1 + f 0 = 1 := by
      have h20₂ := h0 1
      norm_num at h20₂ ⊢
      <;> linarith
    have h20₃ : f 0 = 96 := by
      linarith
    exact h20₃
  
  have h21 : f 20 = 306 := by
    have h21₁ : f 20 + f 19 = 400 := by
      have h21₂ := h0 20
      norm_num at h21₂ ⊢
      <;> linarith
    have h21₃ : f 20 = 306 := by
      linarith
    exact h21₃
  
  have h22 : f 21 = 135 := by
    have h22₁ : f 21 + f 20 = 441 := by
      have h22₂ := h0 21
      norm_num at h22₂ ⊢
      <;> linarith
    have h22₃ : f 21 = 135 := by
      linarith
    exact h22₃
  
  have h23 : f 22 = 349 := by
    have h23₁ : f 22 + f 21 = 484 := by
      have h23₂ := h0 22
      norm_num at h23₂ ⊢
      <;> linarith
    have h23₃ : f 22 = 349 := by
      linarith
    exact h23₃
  
  have h24 : f 23 = 180 := by
    have h24₁ : f 23 + f 22 = 529 := by
      have h24₂ := h0 23
      norm_num at h24₂ ⊢
      <;> linarith
    have h24₃ : f 23 = 180 := by
      linarith
    exact h24₃
  
  have h25 : f 24 = 396 := by
    have h25₁ : f 24 + f 23 = 576 := by
      have h25₂ := h0 24
      norm_num at h25₂ ⊢
      <;> linarith
    have h25₃ : f 24 = 396 := by
      linarith
    exact h25₃
  
  have h26 : f 25 = 229 := by
    have h26₁ : f 25 + f 24 = 625 := by
      have h26₂ := h0 25
      norm_num at h26₂ ⊢
      <;> linarith
    have h26₃ : f 25 = 229 := by
      linarith
    exact h26₃
  
  have h27 : f 26 = 447 := by
    have h27₁ : f 26 + f 25 = 676 := by
      have h27₂ := h0 26
      norm_num at h27₂ ⊢
      <;> linarith
    have h27₃ : f 26 = 447 := by
      linarith
    exact h27₃
  
  have h28 : f 27 = 282 := by
    have h28₁ : f 27 + f 26 = 729 := by
      have h28₂ := h0 27
      norm_num at h28₂ ⊢
      <;> linarith
    have h28₃ : f 27 = 282 := by
      linarith
    exact h28₃
  
  have h29 : f 28 = 502 := by
    have h29₁ : f 28 + f 27 = 784 := by
      have h29₂ := h0 28
      norm_num at h29₂ ⊢
      <;> linarith
    have h29₃ : f 28 = 502 := by
      linarith
    exact h29₃
  
  have h30 : f 29 = 339 := by
    have h30₁ : f 29 + f 28 = 841 := by
      have h30₂ := h0 29
      norm_num at h30₂ ⊢
      <;> linarith
    have h30₃ : f 29 = 339 := by
      linarith
    exact h30₃
  
  have h31 : f 30 = 561 := by
    have h31₁ : f 30 + f 29 = 900 := by
      have h31₂ := h0 30
      norm_num at h31₂ ⊢
      <;> linarith
    have h31₃ : f 30 = 561 := by
      linarith
    exact h31₃
  
  have h32 : f 94 = 4561 := by
    have h32₁ : f 30 = 561 := h31
    have h32₂ : f 31 = 961 - 561 := by
      have h32₃ := h0 31
      norm_num at h32₃ ⊢
      <;> linarith
    have h32₄ : f 31 = 400 := by
      norm_num at h32₂ ⊢
      <;> linarith
    have h32₅ : f 32 = 1024 - 400 := by
      have h32₆ := h0 32
      norm_num at h32₆ ⊢
      <;> linarith
    have h32₇ : f 32 = 624 := by
      norm_num at h32₅ ⊢
      <;> linarith
    have h32₈ : f 33 = 1089 - 624 := by
      have h32₉ := h0 33
      norm_num at h32₉ ⊢
      <;> linarith
    have h32₁₀ : f 33 = 465 := by
      norm_num at h32₈ ⊢
      <;> linarith
    have h32₁₁ : f 34 = 1156 - 465 := by
      have h32₁₂ := h0 34
      norm_num at h32₁₂ ⊢
      <;> linarith
    have h32₁₃ : f 34 = 691 := by
      norm_num at h32₁₁ ⊢
      <;> linarith
    have h32₁₄ : f 35 = 1225 - 691 := by
      have h32₁₅ := h0 35
      norm_num at h32₁₅ ⊢
      <;> linarith
    have h32₁₆ : f 35 = 534 := by
      norm_num at h32₁₄ ⊢
      <;> linarith
    have h32₁₇ : f 36 = 1296 - 534 := by
      have h32₁₈ := h0 36
      norm_num at h32₁₈ ⊢
      <;> linarith
    have h32₁₉ : f 36 = 762 := by
      norm_num at h32₁₇ ⊢
      <;> linarith
    have h32₂₀ : f 37 = 1369 - 762 := by
      have h32₂₁ := h0 37
      norm_num at h32₂₁ ⊢
      <;> linarith
    have h32₂₂ : f 37 = 607 := by
      norm_num at h32₂₀ ⊢
      <;> linarith
    have h32₂₃ : f 38 = 1444 - 607 := by
      have h32₂₄ := h0 38
      norm_num at h32₂₄ ⊢
      <;> linarith
    have h32₂₅ : f 38 = 837 := by
      norm_num at h32₂₃ ⊢
      <;> linarith
    have h32₂₆ : f 39 = 1521 - 837 := by
      have h32₂₇ := h0 39
      norm_num at h32₂₇ ⊢
      <;> linarith
    have h32₂₈ : f 39 = 684 := by
      norm_num at h32₂₆ ⊢
      <;> linarith
    have h32₂₉ : f 40 = 1600 - 684 := by
      have h32₃₀ := h0 40
      norm_num at h32₃₀ ⊢
      <;> linarith
    have h32₃₁ : f 40 = 916 := by
      norm_num at h32₂₉ ⊢
      <;> linarith
    have h32₃₂ : f 41 = 1681 - 916 := by
      have h32₃₃ := h0 41
      norm_num at h32₃₃ ⊢
      <;> linarith
    have h32₃₄ : f 41 = 765 := by
      norm_num at h32₃₂ ⊢
      <;> linarith
    have h32₃₅ : f 42 = 1764 - 765 := by
      have h32₃₆ := h0 42
      norm_num at h32₃₆ ⊢
      <;> linarith
    have h32₃₇ : f 42 = 999 := by
      norm_num at h32₃₅ ⊢
      <;> linarith
    have h32₃₈ : f 43 = 1849 - 999 := by
      have h32₃₉ := h0 43
      norm_num at h32₃₉ ⊢
      <;> linarith
    have h32₄₀ : f 43 = 850 := by
      norm_num at h32₃₈ ⊢
      <;> linarith
    have h32₄₁ : f 44 = 1936 - 850 := by
      have h32₄₂ := h0 44
      norm_num at h32₄₂ ⊢
      <;> linarith
    have h32₄₃ : f 44 = 1086 := by
      norm_num at h32₄₁ ⊢
      <;> linarith
    have h32₄₄ : f 45 = 2025 - 1086 := by
      have h32₄₅ := h0 45
      norm_num at h32₄₅ ⊢
      <;> linarith
    have h32₄₆ : f 45 = 939 := by
      norm_num at h32₄₄ ⊢
      <;> linarith
    have h32₄₇ : f 46 = 2116 - 939 := by
      have h32₄₈ := h0 46
      norm_num at h32₄₈ ⊢
      <;> linarith
    have h32₄₉ : f 46 = 1177 := by
      norm_num at h32₄₇ ⊢
      <;> linarith
    have h32₅₀ : f 47 = 2209 - 1177 := by
      have h32₅₁ := h0 47
      norm_num at h32₅₁ ⊢
      <;> linarith
    have h32₅₂ : f 47 = 1032 := by
      norm_num at h32₅₀ ⊢
      <;> linarith
    have h32₅₃ : f 48 = 2304 - 1032 := by
      have h32₅₄ := h0 48
      norm_num at h32₅₄ ⊢
      <;> linarith
    have h32₅₅ : f 48 = 1272 := by
      norm_num at h32₅₃ ⊢
      <;> linarith
    have h32₅₆ : f 49 = 2401 - 1272 := by
      have h32₅₇ := h0 49
      norm_num at h32₅₇ ⊢
      <;> linarith
    have h32₅₈ : f 49 = 1129 := by
      norm_num at h32₅₆ ⊢
      <;> linarith
    have h32₅₉ : f 50 = 2500 - 1129 := by
      have h32₆₀ := h0 50
      norm_num at h32₆₀ ⊢
      <;> linarith
    have h32₆₁ : f 50 = 1371 := by
      norm_num at h32₅₉ ⊢
      <;> linarith
    have h32₆₂ : f 51 = 2601 - 1371 := by
      have h32₆₃ := h0 51
      norm_num at h32₆₃ ⊢
      <;> linarith
    have h32₆₄ : f 51 = 1230 := by
      norm_num at h32₆₂ ⊢
      <;> linarith
    have h32₆₅ : f 52 = 2704 - 1230 := by
      have h32₆₆ := h0 52
      norm_num at h32₆₆ ⊢
      <;> linarith
    have h32₆₇ : f 52 = 1474 := by
      norm_num at h32₆₅ ⊢
      <;> linarith
    have h32₆₈ : f 53 = 2809 - 1474 := by
      have h32₆₉ := h0 53
      norm_num at h32₆₉ ⊢
      <;> linarith
    have h32₇₀ : f 53 = 1335 := by
      norm_num at h32₆₈ ⊢
      <;> linarith
    have h32₇₁ : f 54 = 2916 - 1335 := by
      have h32₇₂ := h0 54
      norm_num at h32₇₂ ⊢
      <;> linarith
    have h32₇₃ : f 54 = 1581 := by
      norm_num at h32₇₁ ⊢
      <;> linarith
    have h32₇₄ : f 55 = 3025 - 1581 := by
      have h32₇₅ := h0 55
      norm_num at h32₇₅ ⊢
      <;> linarith
    have h32₇₆ : f 55 = 1444 := by
      norm_num at h32₇₄ ⊢
      <;> linarith
    have h32₇₇ : f 56 = 3136 - 1444 := by
      have h32₇₈ := h0 56
      norm_num at h32₇₈ ⊢
      <;> linarith
    have h32₇₉ : f 56 = 1692 := by
      norm_num at h32₇₇ ⊢
      <;> linarith
    have h32₈₀ : f 57 = 3249 - 1692 := by
      have h32₈₁ := h0 57
      norm_num at h32₈₁ ⊢
      <;> linarith
    have h32₈₂ : f 57 = 1557 := by
      norm_num at h32₈₀ ⊢
      <;> linarith
    have h32₈₃ : f 58 = 3364 - 1557 := by
      have h32₈₄ := h0 58
      norm_num at h32₈₄ ⊢
      <;> linarith
    have h32₈₅ : f 58 = 1807 := by
      norm_num at h32₈₃ ⊢
      <;> linarith
    have h32₈₆ : f 59 = 3481 - 1807 := by
      have h32₈₇ := h0 59
      norm_num at h32₈₇ ⊢
      <;> linarith
    have h32₈₈ : f 59 = 1674 := by
      norm_num at h32₈₆ ⊢
      <;> linarith
    have h32₈₉ : f 60 = 3600 - 1674 := by
      have h32₉₀ := h0 60
      norm_num at h32₉₀ ⊢
      <;> linarith
    have h32₉₁ : f 60 = 1926 := by
      norm_num at h32₈₉ ⊢
      <;> linarith
    have h32₉₂ : f 61 = 3721 - 1926 := by
      have h32₉₃ := h0 61
      norm_num at h32₉₃ ⊢
      <;> linarith
    have h32₉₄ : f 61 = 1795 := by
      norm_num at h32₉₂ ⊢
      <;> linarith
    have h32₉₅ : f 62 = 3844 - 1795 := by
      have h32₉₆ := h0 62
      norm_num at h32₉₆ ⊢
      <;> linarith
    have h32₉₇ : f 62 = 2049 := by
      norm_num at h32₉₅ ⊢
      <;> linarith
    have h32₉₈ : f 63 = 3969 - 2049 := by
      have h32₉₉ := h0 63
      norm_num at h32₉₉ ⊢
      <;> linarith
    have h33₀ : f 63 = 1920 := by
      norm_num at h32₉₈ ⊢
      <;> linarith
    have h33₁ : f 64 = 4096 - 1920 := by
      have h33₂ := h0 64
      norm_num at h33₂ ⊢
      <;> linarith
    have h33₃ : f 64 = 2176 := by
      norm_num at h33₁ ⊢
      <;> linarith
    have h33₄ : f 65 = 4225 - 2176 := by
      have h33₅ := h0 65
      norm_num at h33₅ ⊢
      <;> linarith
    have h33₆ : f 65 = 2049 := by
      norm_num at h33₄ ⊢
      <;> linarith
    have h33₇ : f 66 = 4356 - 2049 := by
      have h33₈ := h0 66
      norm_num at h33₈ ⊢
      <;> linarith
    have h33₉ : f 66 = 2307 := by
      norm_num at h33₇ ⊢
      <;> linarith
    have h34₀ : f 67 = 4489 - 2307 := by
      have h34₁ := h0 67
      norm_num at h34₁ ⊢
      <;> linarith
    have h34₂ : f 67 = 2182 := by
      norm_num at h34₀ ⊢
      <;> linarith
    have h34₃ : f 68 = 4624 - 2182 := by
      have h34₄ := h0 68
      norm_num at h34₄ ⊢
      <;> linarith
    have h34₅ : f 68 = 2442 := by
      norm_num at h34₃ ⊢
      <;> linarith
    have h34₆ : f 69 = 4761 - 2442 := by
      have h34₇ := h0 69
      norm_num at h34₇ ⊢
      <;> linarith
    have h34₈ : f 69 = 2319 := by
      norm_num at h34₆ ⊢
      <;> linarith
    have h34₉ : f 70 = 4900 - 2319 := by
      have h35₀ := h0 70
      norm_num at h35₀ ⊢
      <;> linarith
    have h35₁ : f 70 = 2581 := by
      norm_num at h34₉ ⊢
      <;> linarith
    have h35₂ : f 71 = 5041 - 2581 := by
      have h35₃ := h0 71
      norm_num at h35₃ ⊢
      <;> linarith
    have h35₄ : f 71 = 2460 := by
      norm_num at h35₂ ⊢
      <;> linarith
    have h35₅ : f 72 = 5184 - 2460 := by
      have h35₆ := h0 72
      norm_num at h35₆ ⊢
      <;> linarith
    have h35₇ : f 72 = 2724 := by
      norm_num at h35₅ ⊢
      <;> linarith
    have h35₈ : f 73 = 5329 - 2724 := by
      have h35₉ := h0 73
      norm_num at h35₉ ⊢
      <;> linarith
    have h36₀ : f 73 = 2605 := by
      norm_num at h35₈ ⊢
      <;> linarith
    have h36₁ : f 74 = 5476 - 2605 := by
      have h36₂ := h0 74
      norm_num at h36₂ ⊢
      <;> linarith
    have h36₃ : f 74 = 2871 := by
      norm_num at h36₁ ⊢
      <;> linarith
    have h36₄ : f 75 = 5625 - 2871 := by
      have h36₅ := h0 75
      norm_num at h36₅ ⊢
      <;> linarith
    have h36₆ : f 75 = 2754 := by
      norm_num at h36₄ ⊢
      <;> linarith
    have h36₇ : f 76 = 5776 - 2754 := by
      have h36₈ := h0 76
      norm_num at h36₈ ⊢
      <;> linarith
    have h36₉ : f 76 = 3022 := by
      norm_num at h36₇ ⊢
      <;> linarith
    have h37₀ : f 77 = 5929 - 3022 := by
      have h37₁ := h0 77
      norm_num at h37₁ ⊢
      <;> linarith
    have h37₂ : f 77 = 2907 := by
      norm_num at h37₀ ⊢
      <;> linarith
    have h37₃ : f 78 = 6084 - 2907 := by
      have h37₄ := h0 78
      norm_num at h37₄ ⊢
      <;> linarith
    have h37₅ : f 78 = 3177 := by
      norm_num at h37₃ ⊢
      <;> linarith
    have h37₆ : f 79 = 6241 - 3177 := by
      have h37₇ := h0 79
      norm_num at h37₇ ⊢
      <;> linarith
    have h37₈ : f 79 = 3064 := by
      norm_num at h37₆ ⊢
      <;> linarith
    have h37₉ : f 80 = 6400 - 3064 := by
      have h38₀ := h0 80
      norm_num at h38₀ ⊢
      <;> linarith
    have h38₁ : f 80 = 3336 := by
      norm_num at h37₉ ⊢
      <;> linarith
    have h38₂ : f 81 = 6561 - 3336 := by
      have h38₃ := h0 81
      norm_num at h38₃ ⊢
      <;> linarith
    have h38₄ : f 81 = 3225 := by
      norm_num at h38₂ ⊢
      <;> linarith
    have h38₅ : f 82 = 6724 - 3225 := by
      have h38₆ := h0 82
      norm_num at h38₆ ⊢
      <;> linarith
    have h38₇ : f 82 = 3499 := by
      norm_num at h38₅ ⊢
      <;> linarith
    have h38₈ : f 83 = 6889 - 3499 := by
      have h38₉ := h0 83
      norm_num at h38₉ ⊢
      <;> linarith
    have h39₀ : f 83 = 3390 := by
      norm_num at h38₈ ⊢
      <;> linarith
    have h39₁ : f 84 = 7056 - 3390 := by
      have h39₂ := h0 84
      norm_num at h39₂ ⊢
      <;> linarith
    have h39₃ : f 84 = 3666 := by
      norm_num at h39₁ ⊢
      <;> linarith
    have h39₄ : f 85 = 7225 - 3666 := by
      have h39₅ := h0 85
      norm_num at h39₅ ⊢
      <;> linarith
    have h39₆ : f 85 = 3559 := by
      norm_num at h39₄ ⊢
      <;> linarith
    have h39₇ : f 86 = 7396 - 3559 := by
      have h39₈ := h0 86
      norm_num at h39₈ ⊢
      <;> linarith
    have h39₉ : f 86 = 3837 := by
      norm_num at h39₇ ⊢
      <;> linarith
    have h40₀ : f 87 = 7569 - 3837 := by
      have h40₁ := h0 87
      norm_num at h40₁ ⊢
      <;> linarith
    have h40₂ : f 87 = 3732 := by
      norm_num at h40₀ ⊢
      <;> linarith
    have h40₃ : f 88 = 7744 - 3732 := by
      have h40₄ := h0 88
      norm_num at h40₄ ⊢
      <;> linarith
    have h40₅ : f 88 = 4012 := by
      norm_num at h40₃ ⊢
      <;> linarith
    have h40₆ : f 89 = 7921 - 4012 := by
      have h40₇ := h0 89
      norm_num at h40₇ ⊢
      <;> linarith
    have h40₈ : f 89 = 3909 := by
      norm_num at h40₆ ⊢
      <;> linarith
    have h40₉ : f 90 = 8100 - 3909 := by
      have h41₀ := h0 90
      norm_num at h41₀ ⊢
      <;> linarith
    have h41₁ : f 90 = 4191 := by
      norm_num at h40₉ ⊢
      <;> linarith
    have h41₂ : f 91 = 8281 - 4191 := by
      have h41₃ := h0 91
      norm_num at h41₃ ⊢
      <;> linarith
    have h41₄ : f 91 = 4090 := by
      norm_num at h41₂ ⊢
      <;> linarith
    have h41₅ : f 92 = 8464 - 4090 := by
      have h41₆ := h0 92
      norm_num at h41₆ ⊢
      <;> linarith
    have h41₇ : f 92 = 4374 := by
      norm_num at h41₅ ⊢
      <;> linarith
    have h41₈ : f 93 = 8649 - 4374 := by
      have h41₉ := h0 93
      norm_num at h41₉ ⊢
      <;> linarith
    have h42₀ : f 93 = 4275 := by
      norm_num at h41₈ ⊢
      <;> linarith
    have h42₁ : f 94 = 8836 - 4275 := by
      have h42₂ := h0 94
      norm_num at h42₂ ⊢
      <;> linarith
    have h42₃ : f 94 = 4561 := by
      norm_num at h42₁ ⊢
      <;> linarith
    exact h42₃
  
  have h33 : f 94 % 1000 = 561 := by
    have h33₁ : f 94 = 4561 := h32
    have h33₂ : f 94 % 1000 = 561 := by
      norm_num [h33₁]
      <;> rfl
    exact h33₂
  
  exact h33