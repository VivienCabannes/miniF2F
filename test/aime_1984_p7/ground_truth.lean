import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Rat

theorem aime_1984_p7
  (f : ℤ → ℤ)
  (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
  (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) :
  f 84 = 997 := by
  have h₂ : f 1004 = 1001 := by
    have h₂₁ : f 1004 = 1004 - 3 := by
      apply h₀
      <;> norm_num
    rw [h₂₁]
    <;> norm_num
  
  have h₃ : f 1003 = 1000 := by
    have h₃₁ : f 1003 = 1003 - 3 := by
      apply h₀
      <;> norm_num
    rw [h₃₁]
    <;> norm_num
  
  have h₄ : f 1002 = 999 := by
    have h₄₁ : f 1002 = 1002 - 3 := by
      apply h₀
      <;> norm_num
    rw [h₄₁]
    <;> norm_num
  
  have h₅ : f 1001 = 998 := by
    have h₅₁ : f 1001 = 1001 - 3 := by
      apply h₀
      <;> norm_num
    rw [h₅₁]
    <;> norm_num
  
  have h₆ : f 1000 = 997 := by
    have h₆₁ : f 1000 = 1000 - 3 := by
      apply h₀
      <;> norm_num
    rw [h₆₁]
    <;> norm_num
  
  have h₇ : f 999 = 998 := by
    have h₇₁ : f 999 = f (f (999 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₁]
    have h₇₂ : f (999 + 5) = f 1004 := by norm_num
    rw [h₇₂]
    rw [h₂]
    <;> norm_num
    <;> linarith
  
  have h₈ : f 998 = 997 := by
    have h₈₁ : f 998 = f (f (998 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₁]
    have h₈₂ : f (998 + 5) = f 1003 := by norm_num
    rw [h₈₂]
    rw [h₃]
    <;> norm_num
    <;> linarith
  
  have h₉ : f 997 = 998 := by
    have h₉₁ : f 997 = f (f (997 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₁]
    have h₉₂ : f (997 + 5) = f 1002 := by norm_num
    rw [h₉₂]
    rw [h₄]
    <;> norm_num
    <;> linarith
  
  have h₁₀ : f 996 = 997 := by
    have h₁₀₁ : f 996 = f (f (996 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₁]
    have h₁₀₂ : f (996 + 5) = f 1001 := by norm_num
    rw [h₁₀₂]
    rw [h₅]
    <;> norm_num
    <;> linarith
  
  have h₁₁ : f 995 = 998 := by
    have h₁₁₁ : f 995 = f (f (995 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₁]
    have h₁₁₂ : f (995 + 5) = f 1000 := by norm_num
    rw [h₁₁₂]
    rw [h₆]
    <;> norm_num
    <;> linarith
  
  have h₁₂ : f 994 = 997 := by
    have h₁₂₁ : f 994 = f (f (994 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₁]
    have h₁₂₂ : f (994 + 5) = f 999 := by norm_num
    rw [h₁₂₂]
    rw [h₇]
    <;> norm_num
    <;> linarith
  
  have h₁₃ : f 989 = 998 := by
    have h₁₃₁ : f 989 = f (f (989 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₁]
    have h₁₃₂ : f (989 + 5) = f 994 := by norm_num
    rw [h₁₃₂]
    rw [h₁₂]
    <;> norm_num
    <;> linarith
  
  have h₁₄ : f 984 = 997 := by
    have h₁₄₁ : f 984 = f (f (984 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₁]
    have h₁₄₂ : f (984 + 5) = f 989 := by norm_num
    rw [h₁₄₂]
    rw [h₁₃]
    <;> norm_num
    <;> linarith
  
  have h₁₅ : f 979 = 998 := by
    have h₁₅₁ : f 979 = f (f (979 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₁]
    have h₁₅₂ : f (979 + 5) = f 984 := by norm_num
    rw [h₁₅₂]
    rw [h₁₄]
    <;> norm_num
    <;> linarith
  
  have h₁₆ : f 974 = 997 := by
    have h₁₆₁ : f 974 = f (f (974 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₁]
    have h₁₆₂ : f (974 + 5) = f 979 := by norm_num
    rw [h₁₆₂]
    rw [h₁₅]
    <;> norm_num
    <;> linarith
  
  have h₁₇ : f 969 = 998 := by
    have h₁₇₁ : f 969 = f (f (969 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₁]
    have h₁₇₂ : f (969 + 5) = f 974 := by norm_num
    rw [h₁₇₂]
    rw [h₁₆]
    <;> norm_num
    <;> linarith
  
  have h₁₈ : f 964 = 997 := by
    have h₁₈₁ : f 964 = f (f (964 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₁]
    have h₁₈₂ : f (964 + 5) = f 969 := by norm_num
    rw [h₁₈₂]
    rw [h₁₇]
    <;> norm_num
    <;> linarith
  
  have h₁₉ : f 959 = 998 := by
    have h₁₉₁ : f 959 = f (f (959 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₉₁]
    have h₁₉₂ : f (959 + 5) = f 964 := by norm_num
    rw [h₁₉₂]
    rw [h₁₈]
    <;> norm_num
    <;> linarith
  
  have h₂₀ : f 954 = 997 := by
    have h₂₀₁ : f 954 = f (f (954 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₀₁]
    have h₂₀₂ : f (954 + 5) = f 959 := by norm_num
    rw [h₂₀₂]
    rw [h₁₉]
    <;> norm_num
    <;> linarith
  
  have h₂₁ : f 949 = 998 := by
    have h₂₁₁ : f 949 = f (f (949 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₁₁]
    have h₂₁₂ : f (949 + 5) = f 954 := by norm_num
    rw [h₂₁₂]
    rw [h₂₀]
    <;> norm_num
    <;> linarith
  
  have h₂₂ : f 944 = 997 := by
    have h₂₂₁ : f 944 = f (f (944 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₂₁]
    have h₂₂₂ : f (944 + 5) = f 949 := by norm_num
    rw [h₂₂₂]
    rw [h₂₁]
    <;> norm_num
    <;> linarith
  
  have h₂₃ : f 939 = 998 := by
    have h₂₃₁ : f 939 = f (f (939 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₃₁]
    have h₂₃₂ : f (939 + 5) = f 944 := by norm_num
    rw [h₂₃₂]
    rw [h₂₂]
    <;> norm_num
    <;> linarith
  
  have h₂₄ : f 934 = 997 := by
    have h₂₄₁ : f 934 = f (f (934 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₄₁]
    have h₂₄₂ : f (934 + 5) = f 939 := by norm_num
    rw [h₂₄₂]
    rw [h₂₃]
    <;> norm_num
    <;> linarith
  
  have h₂₅ : f 929 = 998 := by
    have h₂₅₁ : f 929 = f (f (929 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₅₁]
    have h₂₅₂ : f (929 + 5) = f 934 := by norm_num
    rw [h₂₅₂]
    rw [h₂₄]
    <;> norm_num
    <;> linarith
  
  have h₂₆ : f 924 = 997 := by
    have h₂₆₁ : f 924 = f (f (924 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₆₁]
    have h₂₆₂ : f (924 + 5) = f 929 := by norm_num
    rw [h₂₆₂]
    rw [h₂₅]
    <;> norm_num
    <;> linarith
  
  have h₂₇ : f 919 = 998 := by
    have h₂₇₁ : f 919 = f (f (919 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₇₁]
    have h₂₇₂ : f (919 + 5) = f 924 := by norm_num
    rw [h₂₇₂]
    rw [h₂₆]
    <;> norm_num
    <;> linarith
  
  have h₂₈ : f 914 = 997 := by
    have h₂₈₁ : f 914 = f (f (914 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₈₁]
    have h₂₈₂ : f (914 + 5) = f 919 := by norm_num
    rw [h₂₈₂]
    rw [h₂₇]
    <;> norm_num
    <;> linarith
  
  have h₂₉ : f 909 = 998 := by
    have h₂₉₁ : f 909 = f (f (909 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₂₉₁]
    have h₂₉₂ : f (909 + 5) = f 914 := by norm_num
    rw [h₂₉₂]
    rw [h₂₈]
    <;> norm_num
    <;> linarith
  
  have h₃₀ : f 904 = 997 := by
    have h₃₀₁ : f 904 = f (f (904 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₀₁]
    have h₃₀₂ : f (904 + 5) = f 909 := by norm_num
    rw [h₃₀₂]
    rw [h₂₉]
    <;> norm_num
    <;> linarith
  
  have h₃₁ : f 899 = 998 := by
    have h₃₁₁ : f 899 = f (f (899 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₁₁]
    have h₃₁₂ : f (899 + 5) = f 904 := by norm_num
    rw [h₃₁₂]
    rw [h₃₀]
    <;> norm_num
    <;> linarith
  
  have h₃₂ : f 894 = 997 := by
    have h₃₂₁ : f 894 = f (f (894 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₂₁]
    have h₃₂₂ : f (894 + 5) = f 899 := by norm_num
    rw [h₃₂₂]
    rw [h₃₁]
    <;> norm_num
    <;> linarith
  
  have h₃₃ : f 889 = 998 := by
    have h₃₃₁ : f 889 = f (f (889 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₃₁]
    have h₃₃₂ : f (889 + 5) = f 894 := by norm_num
    rw [h₃₃₂]
    rw [h₃₂]
    <;> norm_num
    <;> linarith
  
  have h₃₄ : f 884 = 997 := by
    have h₃₄₁ : f 884 = f (f (884 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₄₁]
    have h₃₄₂ : f (884 + 5) = f 889 := by norm_num
    rw [h₃₄₂]
    rw [h₃₃]
    <;> norm_num
    <;> linarith
  
  have h₃₅ : f 879 = 998 := by
    have h₃₅₁ : f 879 = f (f (879 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₅₁]
    have h₃₅₂ : f (879 + 5) = f 884 := by norm_num
    rw [h₃₅₂]
    rw [h₃₄]
    <;> norm_num
    <;> linarith
  
  have h₃₆ : f 874 = 997 := by
    have h₃₆₁ : f 874 = f (f (874 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₆₁]
    have h₃₆₂ : f (874 + 5) = f 879 := by norm_num
    rw [h₃₆₂]
    rw [h₃₅]
    <;> norm_num
    <;> linarith
  
  have h₃₇ : f 869 = 998 := by
    have h₃₇₁ : f 869 = f (f (869 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₇₁]
    have h₃₇₂ : f (869 + 5) = f 874 := by norm_num
    rw [h₃₇₂]
    rw [h₃₆]
    <;> norm_num
    <;> linarith
  
  have h₃₈ : f 864 = 997 := by
    have h₃₈₁ : f 864 = f (f (864 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₈₁]
    have h₃₈₂ : f (864 + 5) = f 869 := by norm_num
    rw [h₃₈₂]
    rw [h₃₇]
    <;> norm_num
    <;> linarith
  
  have h₃₉ : f 859 = 998 := by
    have h₃₉₁ : f 859 = f (f (859 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₃₉₁]
    have h₃₉₂ : f (859 + 5) = f 864 := by norm_num
    rw [h₃₉₂]
    rw [h₃₈]
    <;> norm_num
    <;> linarith
  
  have h₄₀ : f 854 = 997 := by
    have h₄₀₁ : f 854 = f (f (854 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₀₁]
    have h₄₀₂ : f (854 + 5) = f 859 := by norm_num
    rw [h₄₀₂]
    rw [h₃₉]
    <;> norm_num
    <;> linarith
  
  have h₄₁ : f 849 = 998 := by
    have h₄₁₁ : f 849 = f (f (849 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₁₁]
    have h₄₁₂ : f (849 + 5) = f 854 := by norm_num
    rw [h₄₁₂]
    rw [h₄₀]
    <;> norm_num
    <;> linarith
  
  have h₄₂ : f 844 = 997 := by
    have h₄₂₁ : f 844 = f (f (844 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₂₁]
    have h₄₂₂ : f (844 + 5) = f 849 := by norm_num
    rw [h₄₂₂]
    rw [h₄₁]
    <;> norm_num
    <;> linarith
  
  have h₄₃ : f 839 = 998 := by
    have h₄₃₁ : f 839 = f (f (839 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₃₁]
    have h₄₃₂ : f (839 + 5) = f 844 := by norm_num
    rw [h₄₃₂]
    rw [h₄₂]
    <;> norm_num
    <;> linarith
  
  have h₄₄ : f 834 = 997 := by
    have h₄₄₁ : f 834 = f (f (834 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₄₁]
    have h₄₄₂ : f (834 + 5) = f 839 := by norm_num
    rw [h₄₄₂]
    rw [h₄₃]
    <;> norm_num
    <;> linarith
  
  have h₄₅ : f 829 = 998 := by
    have h₄₅₁ : f 829 = f (f (829 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₅₁]
    have h₄₅₂ : f (829 + 5) = f 834 := by norm_num
    rw [h₄₅₂]
    rw [h₄₄]
    <;> norm_num
    <;> linarith
  
  have h₄₆ : f 824 = 997 := by
    have h₄₆₁ : f 824 = f (f (824 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₆₁]
    have h₄₆₂ : f (824 + 5) = f 829 := by norm_num
    rw [h₄₆₂]
    rw [h₄₅]
    <;> norm_num
    <;> linarith
  
  have h₄₇ : f 819 = 998 := by
    have h₄₇₁ : f 819 = f (f (819 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₇₁]
    have h₄₇₂ : f (819 + 5) = f 824 := by norm_num
    rw [h₄₇₂]
    rw [h₄₆]
    <;> norm_num
    <;> linarith
  
  have h₄₈ : f 814 = 997 := by
    have h₄₈₁ : f 814 = f (f (814 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₈₁]
    have h₄₈₂ : f (814 + 5) = f 819 := by norm_num
    rw [h₄₈₂]
    rw [h₄₇]
    <;> norm_num
    <;> linarith
  
  have h₄₉ : f 809 = 998 := by
    have h₄₉₁ : f 809 = f (f (809 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₄₉₁]
    have h₄₉₂ : f (809 + 5) = f 814 := by norm_num
    rw [h₄₉₂]
    rw [h₄₈]
    <;> norm_num
    <;> linarith
  
  have h₅₀ : f 804 = 997 := by
    have h₅₀₁ : f 804 = f (f (804 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₀₁]
    have h₅₀₂ : f (804 + 5) = f 809 := by norm_num
    rw [h₅₀₂]
    rw [h₄₉]
    <;> norm_num
    <;> linarith
  
  have h₅₁ : f 799 = 998 := by
    have h₅₁₁ : f 799 = f (f (799 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₁₁]
    have h₅₁₂ : f (799 + 5) = f 804 := by norm_num
    rw [h₅₁₂]
    rw [h₅₀]
    <;> norm_num
    <;> linarith
  
  have h₅₂ : f 794 = 997 := by
    have h₅₂₁ : f 794 = f (f (794 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₂₁]
    have h₅₂₂ : f (794 + 5) = f 799 := by norm_num
    rw [h₅₂₂]
    rw [h₅₁]
    <;> norm_num
    <;> linarith
  
  have h₅₃ : f 789 = 998 := by
    have h₅₃₁ : f 789 = f (f (789 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₃₁]
    have h₅₃₂ : f (789 + 5) = f 794 := by norm_num
    rw [h₅₃₂]
    rw [h₅₂]
    <;> norm_num
    <;> linarith
  
  have h₅₄ : f 784 = 997 := by
    have h₅₄₁ : f 784 = f (f (784 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₄₁]
    have h₅₄₂ : f (784 + 5) = f 789 := by norm_num
    rw [h₅₄₂]
    rw [h₅₃]
    <;> norm_num
    <;> linarith
  
  have h₅₅ : f 779 = 998 := by
    have h₅₅₁ : f 779 = f (f (779 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₅₁]
    have h₅₅₂ : f (779 + 5) = f 784 := by norm_num
    rw [h₅₅₂]
    rw [h₅₄]
    <;> norm_num
    <;> linarith
  
  have h₅₆ : f 774 = 997 := by
    have h₅₆₁ : f 774 = f (f (774 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₆₁]
    have h₅₆₂ : f (774 + 5) = f 779 := by norm_num
    rw [h₅₆₂]
    rw [h₅₅]
    <;> norm_num
    <;> linarith
  
  have h₅₇ : f 769 = 998 := by
    have h₅₇₁ : f 769 = f (f (769 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₇₁]
    have h₅₇₂ : f (769 + 5) = f 774 := by norm_num
    rw [h₅₇₂]
    rw [h₅₆]
    <;> norm_num
    <;> linarith
  
  have h₅₈ : f 764 = 997 := by
    have h₅₈₁ : f 764 = f (f (764 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₈₁]
    have h₅₈₂ : f (764 + 5) = f 769 := by norm_num
    rw [h₅₈₂]
    rw [h₅₇]
    <;> norm_num
    <;> linarith
  
  have h₅₉ : f 759 = 998 := by
    have h₅₉₁ : f 759 = f (f (759 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₅₉₁]
    have h₅₉₂ : f (759 + 5) = f 764 := by norm_num
    rw [h₅₉₂]
    rw [h₅₈]
    <;> norm_num
    <;> linarith
  
  have h₆₀ : f 754 = 997 := by
    have h₆₀₁ : f 754 = f (f (754 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₀₁]
    have h₆₀₂ : f (754 + 5) = f 759 := by norm_num
    rw [h₆₀₂]
    rw [h₅₉]
    <;> norm_num
    <;> linarith
  
  have h₆₁ : f 749 = 998 := by
    have h₆₁₁ : f 749 = f (f (749 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₁₁]
    have h₆₁₂ : f (749 + 5) = f 754 := by norm_num
    rw [h₆₁₂]
    rw [h₆₀]
    <;> norm_num
    <;> linarith
  
  have h₆₂ : f 744 = 997 := by
    have h₆₂₁ : f 744 = f (f (744 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₂₁]
    have h₆₂₂ : f (744 + 5) = f 749 := by norm_num
    rw [h₆₂₂]
    rw [h₆₁]
    <;> norm_num
    <;> linarith
  
  have h₆₃ : f 739 = 998 := by
    have h₆₃₁ : f 739 = f (f (739 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₃₁]
    have h₆₃₂ : f (739 + 5) = f 744 := by norm_num
    rw [h₆₃₂]
    rw [h₆₂]
    <;> norm_num
    <;> linarith
  
  have h₆₄ : f 734 = 997 := by
    have h₆₄₁ : f 734 = f (f (734 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₄₁]
    have h₆₄₂ : f (734 + 5) = f 739 := by norm_num
    rw [h₆₄₂]
    rw [h₆₃]
    <;> norm_num
    <;> linarith
  
  have h₆₅ : f 729 = 998 := by
    have h₆₅₁ : f 729 = f (f (729 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₅₁]
    have h₆₅₂ : f (729 + 5) = f 734 := by norm_num
    rw [h₆₅₂]
    rw [h₆₄]
    <;> norm_num
    <;> linarith
  
  have h₆₆ : f 724 = 997 := by
    have h₆₆₁ : f 724 = f (f (724 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₆₁]
    have h₆₆₂ : f (724 + 5) = f 729 := by norm_num
    rw [h₆₆₂]
    rw [h₆₅]
    <;> norm_num
    <;> linarith
  
  have h₆₇ : f 719 = 998 := by
    have h₆₇₁ : f 719 = f (f (719 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₇₁]
    have h₆₇₂ : f (719 + 5) = f 724 := by norm_num
    rw [h₆₇₂]
    rw [h₆₆]
    <;> norm_num
    <;> linarith
  
  have h₆₈ : f 714 = 997 := by
    have h₆₈₁ : f 714 = f (f (714 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₈₁]
    have h₆₈₂ : f (714 + 5) = f 719 := by norm_num
    rw [h₆₈₂]
    rw [h₆₇]
    <;> norm_num
    <;> linarith
  
  have h₆₉ : f 709 = 998 := by
    have h₆₉₁ : f 709 = f (f (709 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₆₉₁]
    have h₆₉₂ : f (709 + 5) = f 714 := by norm_num
    rw [h₆₉₂]
    rw [h₆₈]
    <;> norm_num
    <;> linarith
  
  have h₇₀ : f 704 = 997 := by
    have h₇₀₁ : f 704 = f (f (704 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₀₁]
    have h₇₀₂ : f (704 + 5) = f 709 := by norm_num
    rw [h₇₀₂]
    rw [h₆₉]
    <;> norm_num
    <;> linarith
  
  have h₇₁ : f 699 = 998 := by
    have h₇₁₁ : f 699 = f (f (699 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₁₁]
    have h₇₁₂ : f (699 + 5) = f 704 := by norm_num
    rw [h₇₁₂]
    rw [h₇₀]
    <;> norm_num
    <;> linarith
  
  have h₇₂ : f 694 = 997 := by
    have h₇₂₁ : f 694 = f (f (694 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₂₁]
    have h₇₂₂ : f (694 + 5) = f 699 := by norm_num
    rw [h₇₂₂]
    rw [h₇₁]
    <;> norm_num
    <;> linarith
  
  have h₇₃ : f 689 = 998 := by
    have h₇₃₁ : f 689 = f (f (689 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₃₁]
    have h₇₃₂ : f (689 + 5) = f 694 := by norm_num
    rw [h₇₃₂]
    rw [h₇₂]
    <;> norm_num
    <;> linarith
  
  have h₇₄ : f 684 = 997 := by
    have h₇₄₁ : f 684 = f (f (684 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₄₁]
    have h₇₄₂ : f (684 + 5) = f 689 := by norm_num
    rw [h₇₄₂]
    rw [h₇₃]
    <;> norm_num
    <;> linarith
  
  have h₇₅ : f 679 = 998 := by
    have h₇₅₁ : f 679 = f (f (679 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₅₁]
    have h₇₅₂ : f (679 + 5) = f 684 := by norm_num
    rw [h₇₅₂]
    rw [h₇₄]
    <;> norm_num
    <;> linarith
  
  have h₇₆ : f 674 = 997 := by
    have h₇₆₁ : f 674 = f (f (674 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₆₁]
    have h₇₆₂ : f (674 + 5) = f 679 := by norm_num
    rw [h₇₆₂]
    rw [h₇₅]
    <;> norm_num
    <;> linarith
  
  have h₇₇ : f 669 = 998 := by
    have h₇₇₁ : f 669 = f (f (669 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₇₁]
    have h₇₇₂ : f (669 + 5) = f 674 := by norm_num
    rw [h₇₇₂]
    rw [h₇₆]
    <;> norm_num
    <;> linarith
  
  have h₇₈ : f 664 = 997 := by
    have h₇₈₁ : f 664 = f (f (664 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₈₁]
    have h₇₈₂ : f (664 + 5) = f 669 := by norm_num
    rw [h₇₈₂]
    rw [h₇₇]
    <;> norm_num
    <;> linarith
  
  have h₇₉ : f 659 = 998 := by
    have h₇₉₁ : f 659 = f (f (659 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₇₉₁]
    have h₇₉₂ : f (659 + 5) = f 664 := by norm_num
    rw [h₇₉₂]
    rw [h₇₈]
    <;> norm_num
    <;> linarith
  
  have h₈₀ : f 654 = 997 := by
    have h₈₀₁ : f 654 = f (f (654 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₀₁]
    have h₈₀₂ : f (654 + 5) = f 659 := by norm_num
    rw [h₈₀₂]
    rw [h₇₉]
    <;> norm_num
    <;> linarith
  
  have h₈₁ : f 649 = 998 := by
    have h₈₁₁ : f 649 = f (f (649 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₁₁]
    have h₈₁₂ : f (649 + 5) = f 654 := by norm_num
    rw [h₈₁₂]
    rw [h₈₀]
    <;> norm_num
    <;> linarith
  
  have h₈₂ : f 644 = 997 := by
    have h₈₂₁ : f 644 = f (f (644 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₂₁]
    have h₈₂₂ : f (644 + 5) = f 649 := by norm_num
    rw [h₈₂₂]
    rw [h₈₁]
    <;> norm_num
    <;> linarith
  
  have h₈₃ : f 639 = 998 := by
    have h₈₃₁ : f 639 = f (f (639 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₃₁]
    have h₈₃₂ : f (639 + 5) = f 644 := by norm_num
    rw [h₈₃₂]
    rw [h₈₂]
    <;> norm_num
    <;> linarith
  
  have h₈₄ : f 634 = 997 := by
    have h₈₄₁ : f 634 = f (f (634 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₄₁]
    have h₈₄₂ : f (634 + 5) = f 639 := by norm_num
    rw [h₈₄₂]
    rw [h₈₃]
    <;> norm_num
    <;> linarith
  
  have h₈₅ : f 629 = 998 := by
    have h₈₅₁ : f 629 = f (f (629 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₅₁]
    have h₈₅₂ : f (629 + 5) = f 634 := by norm_num
    rw [h₈₅₂]
    rw [h₈₄]
    <;> norm_num
    <;> linarith
  
  have h₈₆ : f 624 = 997 := by
    have h₈₆₁ : f 624 = f (f (624 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₆₁]
    have h₈₆₂ : f (624 + 5) = f 629 := by norm_num
    rw [h₈₆₂]
    rw [h₈₅]
    <;> norm_num
    <;> linarith
  
  have h₈₇ : f 619 = 998 := by
    have h₈₇₁ : f 619 = f (f (619 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₇₁]
    have h₈₇₂ : f (619 + 5) = f 624 := by norm_num
    rw [h₈₇₂]
    rw [h₈₆]
    <;> norm_num
    <;> linarith
  
  have h₈₈ : f 614 = 997 := by
    have h₈₈₁ : f 614 = f (f (614 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₈₁]
    have h₈₈₂ : f (614 + 5) = f 619 := by norm_num
    rw [h₈₈₂]
    rw [h₈₇]
    <;> norm_num
    <;> linarith
  
  have h₈₉ : f 609 = 998 := by
    have h₈₉₁ : f 609 = f (f (609 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₈₉₁]
    have h₈₉₂ : f (609 + 5) = f 614 := by norm_num
    rw [h₈₉₂]
    rw [h₈₈]
    <;> norm_num
    <;> linarith
  
  have h₉₀ : f 604 = 997 := by
    have h₉₀₁ : f 604 = f (f (604 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₀₁]
    have h₉₀₂ : f (604 + 5) = f 609 := by norm_num
    rw [h₉₀₂]
    rw [h₈₉]
    <;> norm_num
    <;> linarith
  
  have h₉₁ : f 599 = 998 := by
    have h₉₁₁ : f 599 = f (f (599 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₁₁]
    have h₉₁₂ : f (599 + 5) = f 604 := by norm_num
    rw [h₉₁₂]
    rw [h₉₀]
    <;> norm_num
    <;> linarith
  
  have h₉₂ : f 594 = 997 := by
    have h₉₂₁ : f 594 = f (f (594 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₂₁]
    have h₉₂₂ : f (594 + 5) = f 599 := by norm_num
    rw [h₉₂₂]
    rw [h₉₁]
    <;> norm_num
    <;> linarith
  
  have h₉₃ : f 589 = 998 := by
    have h₉₃₁ : f 589 = f (f (589 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₃₁]
    have h₉₃₂ : f (589 + 5) = f 594 := by norm_num
    rw [h₉₃₂]
    rw [h₉₂]
    <;> norm_num
    <;> linarith
  
  have h₉₄ : f 584 = 997 := by
    have h₉₄₁ : f 584 = f (f (584 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₄₁]
    have h₉₄₂ : f (584 + 5) = f 589 := by norm_num
    rw [h₉₄₂]
    rw [h₉₃]
    <;> norm_num
    <;> linarith
  
  have h₉₅ : f 579 = 998 := by
    have h₉₅₁ : f 579 = f (f (579 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₅₁]
    have h₉₅₂ : f (579 + 5) = f 584 := by norm_num
    rw [h₉₅₂]
    rw [h₉₄]
    <;> norm_num
    <;> linarith
  
  have h₉₆ : f 574 = 997 := by
    have h₉₆₁ : f 574 = f (f (574 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₆₁]
    have h₉₆₂ : f (574 + 5) = f 579 := by norm_num
    rw [h₉₆₂]
    rw [h₉₅]
    <;> norm_num
    <;> linarith
  
  have h₉₇ : f 569 = 998 := by
    have h₉₇₁ : f 569 = f (f (569 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₇₁]
    have h₉₇₂ : f (569 + 5) = f 574 := by norm_num
    rw [h₉₇₂]
    rw [h₉₆]
    <;> norm_num
    <;> linarith
  
  have h₉₈ : f 564 = 997 := by
    have h₉₈₁ : f 564 = f (f (564 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₈₁]
    have h₉₈₂ : f (564 + 5) = f 569 := by norm_num
    rw [h₉₈₂]
    rw [h₉₇]
    <;> norm_num
    <;> linarith
  
  have h₉₉ : f 559 = 998 := by
    have h₉₉₁ : f 559 = f (f (559 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₉₉₁]
    have h₉₉₂ : f (559 + 5) = f 564 := by norm_num
    rw [h₉₉₂]
    rw [h₉₈]
    <;> norm_num
    <;> linarith
  
  have h₁₀₀ : f 554 = 997 := by
    have h₁₀₀₁ : f 554 = f (f (554 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₀₁]
    have h₁₀₀₂ : f (554 + 5) = f 559 := by norm_num
    rw [h₁₀₀₂]
    rw [h₉₉]
    <;> norm_num
    <;> linarith
  
  have h₁₀₁ : f 549 = 998 := by
    have h₁₀₁₁ : f 549 = f (f (549 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₁₁]
    have h₁₀₁₂ : f (549 + 5) = f 554 := by norm_num
    rw [h₁₀₁₂]
    rw [h₁₀₀]
    <;> norm_num
    <;> linarith
  
  have h₁₀₂ : f 544 = 997 := by
    have h₁₀₂₁ : f 544 = f (f (544 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₂₁]
    have h₁₀₂₂ : f (544 + 5) = f 549 := by norm_num
    rw [h₁₀₂₂]
    rw [h₁₀₁]
    <;> norm_num
    <;> linarith
  
  have h₁₀₃ : f 539 = 998 := by
    have h₁₀₃₁ : f 539 = f (f (539 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₃₁]
    have h₁₀₃₂ : f (539 + 5) = f 544 := by norm_num
    rw [h₁₀₃₂]
    rw [h₁₀₂]
    <;> norm_num
    <;> linarith
  
  have h₁₀₄ : f 534 = 997 := by
    have h₁₀₄₁ : f 534 = f (f (534 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₄₁]
    have h₁₀₄₂ : f (534 + 5) = f 539 := by norm_num
    rw [h₁₀₄₂]
    rw [h₁₀₃]
    <;> norm_num
    <;> linarith
  
  have h₁₀₅ : f 529 = 998 := by
    have h₁₀₅₁ : f 529 = f (f (529 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₅₁]
    have h₁₀₅₂ : f (529 + 5) = f 534 := by norm_num
    rw [h₁₀₅₂]
    rw [h₁₀₄]
    <;> norm_num
    <;> linarith
  
  have h₁₀₆ : f 524 = 997 := by
    have h₁₀₆₁ : f 524 = f (f (524 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₆₁]
    have h₁₀₆₂ : f (524 + 5) = f 529 := by norm_num
    rw [h₁₀₆₂]
    rw [h₁₀₅]
    <;> norm_num
    <;> linarith
  
  have h₁₀₇ : f 519 = 998 := by
    have h₁₀₇₁ : f 519 = f (f (519 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₇₁]
    have h₁₀₇₂ : f (519 + 5) = f 524 := by norm_num
    rw [h₁₀₇₂]
    rw [h₁₀₆]
    <;> norm_num
    <;> linarith
  
  have h₁₀₈ : f 514 = 997 := by
    have h₁₀₈₁ : f 514 = f (f (514 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₈₁]
    have h₁₀₈₂ : f (514 + 5) = f 519 := by norm_num
    rw [h₁₀₈₂]
    rw [h₁₀₇]
    <;> norm_num
    <;> linarith
  
  have h₁₀₉ : f 509 = 998 := by
    have h₁₀₉₁ : f 509 = f (f (509 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₀₉₁]
    have h₁₀₉₂ : f (509 + 5) = f 514 := by norm_num
    rw [h₁₀₉₂]
    rw [h₁₀₈]
    <;> norm_num
    <;> linarith
  
  have h₁₁₀ : f 504 = 997 := by
    have h₁₁₀₁ : f 504 = f (f (504 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₀₁]
    have h₁₁₀₂ : f (504 + 5) = f 509 := by norm_num
    rw [h₁₁₀₂]
    rw [h₁₀₉]
    <;> norm_num
    <;> linarith
  
  have h₁₁₁ : f 499 = 998 := by
    have h₁₁₁₁ : f 499 = f (f (499 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₁₁]
    have h₁₁₁₂ : f (499 + 5) = f 504 := by norm_num
    rw [h₁₁₁₂]
    rw [h₁₁₀]
    <;> norm_num
    <;> linarith
  
  have h₁₁₂ : f 494 = 997 := by
    have h₁₁₂₁ : f 494 = f (f (494 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₂₁]
    have h₁₁₂₂ : f (494 + 5) = f 499 := by norm_num
    rw [h₁₁₂₂]
    rw [h₁₁₁]
    <;> norm_num
    <;> linarith
  
  have h₁₁₃ : f 489 = 998 := by
    have h₁₁₃₁ : f 489 = f (f (489 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₃₁]
    have h₁₁₃₂ : f (489 + 5) = f 494 := by norm_num
    rw [h₁₁₃₂]
    rw [h₁₁₂]
    <;> norm_num
    <;> linarith
  
  have h₁₁₄ : f 484 = 997 := by
    have h₁₁₄₁ : f 484 = f (f (484 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₄₁]
    have h₁₁₄₂ : f (484 + 5) = f 489 := by norm_num
    rw [h₁₁₄₂]
    rw [h₁₁₃]
    <;> norm_num
    <;> linarith
  
  have h₁₁₅ : f 479 = 998 := by
    have h₁₁₅₁ : f 479 = f (f (479 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₅₁]
    have h₁₁₅₂ : f (479 + 5) = f 484 := by norm_num
    rw [h₁₁₅₂]
    rw [h₁₁₄]
    <;> norm_num
    <;> linarith
  
  have h₁₁₆ : f 474 = 997 := by
    have h₁₁₆₁ : f 474 = f (f (474 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₆₁]
    have h₁₁₆₂ : f (474 + 5) = f 479 := by norm_num
    rw [h₁₁₆₂]
    rw [h₁₁₅]
    <;> norm_num
    <;> linarith
  
  have h₁₁₇ : f 469 = 998 := by
    have h₁₁₇₁ : f 469 = f (f (469 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₇₁]
    have h₁₁₇₂ : f (469 + 5) = f 474 := by norm_num
    rw [h₁₁₇₂]
    rw [h₁₁₆]
    <;> norm_num
    <;> linarith
  
  have h₁₁₈ : f 464 = 997 := by
    have h₁₁₈₁ : f 464 = f (f (464 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₈₁]
    have h₁₁₈₂ : f (464 + 5) = f 469 := by norm_num
    rw [h₁₁₈₂]
    rw [h₁₁₇]
    <;> norm_num
    <;> linarith
  
  have h₁₁₉ : f 459 = 998 := by
    have h₁₁₉₁ : f 459 = f (f (459 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₁₉₁]
    have h₁₁₉₂ : f (459 + 5) = f 464 := by norm_num
    rw [h₁₁₉₂]
    rw [h₁₁₈]
    <;> norm_num
    <;> linarith
  
  have h₁₂₀ : f 454 = 997 := by
    have h₁₂₀₁ : f 454 = f (f (454 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₀₁]
    have h₁₂₀₂ : f (454 + 5) = f 459 := by norm_num
    rw [h₁₂₀₂]
    rw [h₁₁₉]
    <;> norm_num
    <;> linarith
  
  have h₁₂₁ : f 449 = 998 := by
    have h₁₂₁₁ : f 449 = f (f (449 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₁₁]
    have h₁₂₁₂ : f (449 + 5) = f 454 := by norm_num
    rw [h₁₂₁₂]
    rw [h₁₂₀]
    <;> norm_num
    <;> linarith
  
  have h₁₂₂ : f 444 = 997 := by
    have h₁₂₂₁ : f 444 = f (f (444 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₂₁]
    have h₁₂₂₂ : f (444 + 5) = f 449 := by norm_num
    rw [h₁₂₂₂]
    rw [h₁₂₁]
    <;> norm_num
    <;> linarith
  
  have h₁₂₃ : f 439 = 998 := by
    have h₁₂₃₁ : f 439 = f (f (439 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₃₁]
    have h₁₂₃₂ : f (439 + 5) = f 444 := by norm_num
    rw [h₁₂₃₂]
    rw [h₁₂₂]
    <;> norm_num
    <;> linarith
  
  have h₁₂₄ : f 434 = 997 := by
    have h₁₂₄₁ : f 434 = f (f (434 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₄₁]
    have h₁₂₄₂ : f (434 + 5) = f 439 := by norm_num
    rw [h₁₂₄₂]
    rw [h₁₂₃]
    <;> norm_num
    <;> linarith
  
  have h₁₂₅ : f 429 = 998 := by
    have h₁₂₅₁ : f 429 = f (f (429 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₅₁]
    have h₁₂₅₂ : f (429 + 5) = f 434 := by norm_num
    rw [h₁₂₅₂]
    rw [h₁₂₄]
    <;> norm_num
    <;> linarith
  
  have h₁₂₆ : f 424 = 997 := by
    have h₁₂₆₁ : f 424 = f (f (424 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₆₁]
    have h₁₂₆₂ : f (424 + 5) = f 429 := by norm_num
    rw [h₁₂₆₂]
    rw [h₁₂₅]
    <;> norm_num
    <;> linarith
  
  have h₁₂₇ : f 419 = 998 := by
    have h₁₂₇₁ : f 419 = f (f (419 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₇₁]
    have h₁₂₇₂ : f (419 + 5) = f 424 := by norm_num
    rw [h₁₂₇₂]
    rw [h₁₂₆]
    <;> norm_num
    <;> linarith
  
  have h₁₂₈ : f 414 = 997 := by
    have h₁₂₈₁ : f 414 = f (f (414 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₈₁]
    have h₁₂₈₂ : f (414 + 5) = f 419 := by norm_num
    rw [h₁₂₈₂]
    rw [h₁₂₇]
    <;> norm_num
    <;> linarith
  
  have h₁₂₉ : f 409 = 998 := by
    have h₁₂₉₁ : f 409 = f (f (409 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₂₉₁]
    have h₁₂₉₂ : f (409 + 5) = f 414 := by norm_num
    rw [h₁₂₉₂]
    rw [h₁₂₈]
    <;> norm_num
    <;> linarith
  
  have h₁₃₀ : f 404 = 997 := by
    have h₁₃₀₁ : f 404 = f (f (404 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₀₁]
    have h₁₃₀₂ : f (404 + 5) = f 409 := by norm_num
    rw [h₁₃₀₂]
    rw [h₁₂₉]
    <;> norm_num
    <;> linarith
  
  have h₁₃₁ : f 399 = 998 := by
    have h₁₃₁₁ : f 399 = f (f (399 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₁₁]
    have h₁₃₁₂ : f (399 + 5) = f 404 := by norm_num
    rw [h₁₃₁₂]
    rw [h₁₃₀]
    <;> norm_num
    <;> linarith
  
  have h₁₃₂ : f 394 = 997 := by
    have h₁₃₂₁ : f 394 = f (f (394 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₂₁]
    have h₁₃₂₂ : f (394 + 5) = f 399 := by norm_num
    rw [h₁₃₂₂]
    rw [h₁₃₁]
    <;> norm_num
    <;> linarith
  
  have h₁₃₃ : f 389 = 998 := by
    have h₁₃₃₁ : f 389 = f (f (389 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₃₁]
    have h₁₃₃₂ : f (389 + 5) = f 394 := by norm_num
    rw [h₁₃₃₂]
    rw [h₁₃₂]
    <;> norm_num
    <;> linarith
  
  have h₁₃₄ : f 384 = 997 := by
    have h₁₃₄₁ : f 384 = f (f (384 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₄₁]
    have h₁₃₄₂ : f (384 + 5) = f 389 := by norm_num
    rw [h₁₃₄₂]
    rw [h₁₃₃]
    <;> norm_num
    <;> linarith
  
  have h₁₃₅ : f 379 = 998 := by
    have h₁₃₅₁ : f 379 = f (f (379 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₅₁]
    have h₁₃₅₂ : f (379 + 5) = f 384 := by norm_num
    rw [h₁₃₅₂]
    rw [h₁₃₄]
    <;> norm_num
    <;> linarith
  
  have h₁₃₆ : f 374 = 997 := by
    have h₁₃₆₁ : f 374 = f (f (374 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₆₁]
    have h₁₃₆₂ : f (374 + 5) = f 379 := by norm_num
    rw [h₁₃₆₂]
    rw [h₁₃₅]
    <;> norm_num
    <;> linarith
  
  have h₁₃₇ : f 369 = 998 := by
    have h₁₃₇₁ : f 369 = f (f (369 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₇₁]
    have h₁₃₇₂ : f (369 + 5) = f 374 := by norm_num
    rw [h₁₃₇₂]
    rw [h₁₃₆]
    <;> norm_num
    <;> linarith
  
  have h₁₃₈ : f 364 = 997 := by
    have h₁₃₈₁ : f 364 = f (f (364 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₈₁]
    have h₁₃₈₂ : f (364 + 5) = f 369 := by norm_num
    rw [h₁₃₈₂]
    rw [h₁₃₇]
    <;> norm_num
    <;> linarith
  
  have h₁₃₉ : f 359 = 998 := by
    have h₁₃₉₁ : f 359 = f (f (359 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₃₉₁]
    have h₁₃₉₂ : f (359 + 5) = f 364 := by norm_num
    rw [h₁₃₉₂]
    rw [h₁₃₈]
    <;> norm_num
    <;> linarith
  
  have h₁₄₀ : f 354 = 997 := by
    have h₁₄₀₁ : f 354 = f (f (354 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₀₁]
    have h₁₄₀₂ : f (354 + 5) = f 359 := by norm_num
    rw [h₁₄₀₂]
    rw [h₁₃₉]
    <;> norm_num
    <;> linarith
  
  have h₁₄₁ : f 349 = 998 := by
    have h₁₄₁₁ : f 349 = f (f (349 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₁₁]
    have h₁₄₁₂ : f (349 + 5) = f 354 := by norm_num
    rw [h₁₄₁₂]
    rw [h₁₄₀]
    <;> norm_num
    <;> linarith
  
  have h₁₄₂ : f 344 = 997 := by
    have h₁₄₂₁ : f 344 = f (f (344 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₂₁]
    have h₁₄₂₂ : f (344 + 5) = f 349 := by norm_num
    rw [h₁₄₂₂]
    rw [h₁₄₁]
    <;> norm_num
    <;> linarith
  
  have h₁₄₃ : f 339 = 998 := by
    have h₁₄₃₁ : f 339 = f (f (339 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₃₁]
    have h₁₄₃₂ : f (339 + 5) = f 344 := by norm_num
    rw [h₁₄₃₂]
    rw [h₁₄₂]
    <;> norm_num
    <;> linarith
  
  have h₁₄₄ : f 334 = 997 := by
    have h₁₄₄₁ : f 334 = f (f (334 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₄₁]
    have h₁₄₄₂ : f (334 + 5) = f 339 := by norm_num
    rw [h₁₄₄₂]
    rw [h₁₄₃]
    <;> norm_num
    <;> linarith
  
  have h₁₄₅ : f 329 = 998 := by
    have h₁₄₅₁ : f 329 = f (f (329 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₅₁]
    have h₁₄₅₂ : f (329 + 5) = f 334 := by norm_num
    rw [h₁₄₅₂]
    rw [h₁₄₄]
    <;> norm_num
    <;> linarith
  
  have h₁₄₆ : f 324 = 997 := by
    have h₁₄₆₁ : f 324 = f (f (324 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₆₁]
    have h₁₄₆₂ : f (324 + 5) = f 329 := by norm_num
    rw [h₁₄₆₂]
    rw [h₁₄₅]
    <;> norm_num
    <;> linarith
  
  have h₁₄₇ : f 319 = 998 := by
    have h₁₄₇₁ : f 319 = f (f (319 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₇₁]
    have h₁₄₇₂ : f (319 + 5) = f 324 := by norm_num
    rw [h₁₄₇₂]
    rw [h₁₄₆]
    <;> norm_num
    <;> linarith
  
  have h₁₄₈ : f 314 = 997 := by
    have h₁₄₈₁ : f 314 = f (f (314 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₈₁]
    have h₁₄₈₂ : f (314 + 5) = f 319 := by norm_num
    rw [h₁₄₈₂]
    rw [h₁₄₇]
    <;> norm_num
    <;> linarith
  
  have h₁₄₉ : f 309 = 998 := by
    have h₁₄₉₁ : f 309 = f (f (309 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₄₉₁]
    have h₁₄₉₂ : f (309 + 5) = f 314 := by norm_num
    rw [h₁₄₉₂]
    rw [h₁₄₈]
    <;> norm_num
    <;> linarith
  
  have h₁₅₀ : f 304 = 997 := by
    have h₁₅₀₁ : f 304 = f (f (304 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₀₁]
    have h₁₅₀₂ : f (304 + 5) = f 309 := by norm_num
    rw [h₁₅₀₂]
    rw [h₁₄₉]
    <;> norm_num
    <;> linarith
  
  have h₁₅₁ : f 299 = 998 := by
    have h₁₅₁₁ : f 299 = f (f (299 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₁₁]
    have h₁₅₁₂ : f (299 + 5) = f 304 := by norm_num
    rw [h₁₅₁₂]
    rw [h₁₅₀]
    <;> norm_num
    <;> linarith
  
  have h₁₅₂ : f 294 = 997 := by
    have h₁₅₂₁ : f 294 = f (f (294 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₂₁]
    have h₁₅₂₂ : f (294 + 5) = f 299 := by norm_num
    rw [h₁₅₂₂]
    rw [h₁₅₁]
    <;> norm_num
    <;> linarith
  
  have h₁₅₃ : f 289 = 998 := by
    have h₁₅₃₁ : f 289 = f (f (289 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₃₁]
    have h₁₅₃₂ : f (289 + 5) = f 294 := by norm_num
    rw [h₁₅₃₂]
    rw [h₁₅₂]
    <;> norm_num
    <;> linarith
  
  have h₁₅₄ : f 284 = 997 := by
    have h₁₅₄₁ : f 284 = f (f (284 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₄₁]
    have h₁₅₄₂ : f (284 + 5) = f 289 := by norm_num
    rw [h₁₅₄₂]
    rw [h₁₅₃]
    <;> norm_num
    <;> linarith
  
  have h₁₅₅ : f 279 = 998 := by
    have h₁₅₅₁ : f 279 = f (f (279 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₅₁]
    have h₁₅₅₂ : f (279 + 5) = f 284 := by norm_num
    rw [h₁₅₅₂]
    rw [h₁₅₄]
    <;> norm_num
    <;> linarith
  
  have h₁₅₆ : f 274 = 997 := by
    have h₁₅₆₁ : f 274 = f (f (274 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₆₁]
    have h₁₅₆₂ : f (274 + 5) = f 279 := by norm_num
    rw [h₁₅₆₂]
    rw [h₁₅₅]
    <;> norm_num
    <;> linarith
  
  have h₁₅₇ : f 269 = 998 := by
    have h₁₅₇₁ : f 269 = f (f (269 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₇₁]
    have h₁₅₇₂ : f (269 + 5) = f 274 := by norm_num
    rw [h₁₅₇₂]
    rw [h₁₅₆]
    <;> norm_num
    <;> linarith
  
  have h₁₅₈ : f 264 = 997 := by
    have h₁₅₈₁ : f 264 = f (f (264 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₈₁]
    have h₁₅₈₂ : f (264 + 5) = f 269 := by norm_num
    rw [h₁₅₈₂]
    rw [h₁₅₇]
    <;> norm_num
    <;> linarith
  
  have h₁₅₉ : f 259 = 998 := by
    have h₁₅₉₁ : f 259 = f (f (259 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₅₉₁]
    have h₁₅₉₂ : f (259 + 5) = f 264 := by norm_num
    rw [h₁₅₉₂]
    rw [h₁₅₈]
    <;> norm_num
    <;> linarith
  
  have h₁₆₀ : f 254 = 997 := by
    have h₁₆₀₁ : f 254 = f (f (254 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₀₁]
    have h₁₆₀₂ : f (254 + 5) = f 259 := by norm_num
    rw [h₁₆₀₂]
    rw [h₁₅₉]
    <;> norm_num
    <;> linarith
  
  have h₁₆₁ : f 249 = 998 := by
    have h₁₆₁₁ : f 249 = f (f (249 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₁₁]
    have h₁₆₁₂ : f (249 + 5) = f 254 := by norm_num
    rw [h₁₆₁₂]
    rw [h₁₆₀]
    <;> norm_num
    <;> linarith
  
  have h₁₆₂ : f 244 = 997 := by
    have h₁₆₂₁ : f 244 = f (f (244 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₂₁]
    have h₁₆₂₂ : f (244 + 5) = f 249 := by norm_num
    rw [h₁₆₂₂]
    rw [h₁₆₁]
    <;> norm_num
    <;> linarith
  
  have h₁₆₃ : f 239 = 998 := by
    have h₁₆₃₁ : f 239 = f (f (239 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₃₁]
    have h₁₆₃₂ : f (239 + 5) = f 244 := by norm_num
    rw [h₁₆₃₂]
    rw [h₁₆₂]
    <;> norm_num
    <;> linarith
  
  have h₁₆₄ : f 234 = 997 := by
    have h₁₆₄₁ : f 234 = f (f (234 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₄₁]
    have h₁₆₄₂ : f (234 + 5) = f 239 := by norm_num
    rw [h₁₆₄₂]
    rw [h₁₆₃]
    <;> norm_num
    <;> linarith
  
  have h₁₆₅ : f 229 = 998 := by
    have h₁₆₅₁ : f 229 = f (f (229 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₅₁]
    have h₁₆₅₂ : f (229 + 5) = f 234 := by norm_num
    rw [h₁₆₅₂]
    rw [h₁₆₄]
    <;> norm_num
    <;> linarith
  
  have h₁₆₆ : f 224 = 997 := by
    have h₁₆₆₁ : f 224 = f (f (224 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₆₁]
    have h₁₆₆₂ : f (224 + 5) = f 229 := by norm_num
    rw [h₁₆₆₂]
    rw [h₁₆₅]
    <;> norm_num
    <;> linarith
  
  have h₁₆₇ : f 219 = 998 := by
    have h₁₆₇₁ : f 219 = f (f (219 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₇₁]
    have h₁₆₇₂ : f (219 + 5) = f 224 := by norm_num
    rw [h₁₆₇₂]
    rw [h₁₆₆]
    <;> norm_num
    <;> linarith
  
  have h₁₆₈ : f 214 = 997 := by
    have h₁₆₈₁ : f 214 = f (f (214 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₈₁]
    have h₁₆₈₂ : f (214 + 5) = f 219 := by norm_num
    rw [h₁₆₈₂]
    rw [h₁₆₇]
    <;> norm_num
    <;> linarith
  
  have h₁₆₉ : f 209 = 998 := by
    have h₁₆₉₁ : f 209 = f (f (209 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₆₉₁]
    have h₁₆₉₂ : f (209 + 5) = f 214 := by norm_num
    rw [h₁₆₉₂]
    rw [h₁₆₈]
    <;> norm_num
    <;> linarith
  
  have h₁₇₀ : f 204 = 997 := by
    have h₁₇₀₁ : f 204 = f (f (204 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₀₁]
    have h₁₇₀₂ : f (204 + 5) = f 209 := by norm_num
    rw [h₁₇₀₂]
    rw [h₁₆₉]
    <;> norm_num
    <;> linarith
  
  have h₁₇₁ : f 199 = 998 := by
    have h₁₇₁₁ : f 199 = f (f (199 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₁₁]
    have h₁₇₁₂ : f (199 + 5) = f 204 := by norm_num
    rw [h₁₇₁₂]
    rw [h₁₇₀]
    <;> norm_num
    <;> linarith
  
  have h₁₇₂ : f 194 = 997 := by
    have h₁₇₂₁ : f 194 = f (f (194 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₂₁]
    have h₁₇₂₂ : f (194 + 5) = f 199 := by norm_num
    rw [h₁₇₂₂]
    rw [h₁₇₁]
    <;> norm_num
    <;> linarith
  
  have h₁₇₃ : f 189 = 998 := by
    have h₁₇₃₁ : f 189 = f (f (189 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₃₁]
    have h₁₇₃₂ : f (189 + 5) = f 194 := by norm_num
    rw [h₁₇₃₂]
    rw [h₁₇₂]
    <;> norm_num
    <;> linarith
  
  have h₁₇₄ : f 184 = 997 := by
    have h₁₇₄₁ : f 184 = f (f (184 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₄₁]
    have h₁₇₄₂ : f (184 + 5) = f 189 := by norm_num
    rw [h₁₇₄₂]
    rw [h₁₇₃]
    <;> norm_num
    <;> linarith
  
  have h₁₇₅ : f 179 = 998 := by
    have h₁₇₅₁ : f 179 = f (f (179 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₅₁]
    have h₁₇₅₂ : f (179 + 5) = f 184 := by norm_num
    rw [h₁₇₅₂]
    rw [h₁₇₄]
    <;> norm_num
    <;> linarith
  
  have h₁₇₆ : f 174 = 997 := by
    have h₁₇₆₁ : f 174 = f (f (174 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₆₁]
    have h₁₇₆₂ : f (174 + 5) = f 179 := by norm_num
    rw [h₁₇₆₂]
    rw [h₁₇₅]
    <;> norm_num
    <;> linarith
  
  have h₁₇₇ : f 169 = 998 := by
    have h₁₇₇₁ : f 169 = f (f (169 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₇₁]
    have h₁₇₇₂ : f (169 + 5) = f 174 := by norm_num
    rw [h₁₇₇₂]
    rw [h₁₇₆]
    <;> norm_num
    <;> linarith
  
  have h₁₇₈ : f 164 = 997 := by
    have h₁₇₈₁ : f 164 = f (f (164 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₈₁]
    have h₁₇₈₂ : f (164 + 5) = f 169 := by norm_num
    rw [h₁₇₈₂]
    rw [h₁₇₇]
    <;> norm_num
    <;> linarith
  
  have h₁₇₉ : f 159 = 998 := by
    have h₁₇₉₁ : f 159 = f (f (159 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₇₉₁]
    have h₁₇₉₂ : f (159 + 5) = f 164 := by norm_num
    rw [h₁₇₉₂]
    rw [h₁₇₈]
    <;> norm_num
    <;> linarith
  
  have h₁₈₀ : f 154 = 997 := by
    have h₁₈₀₁ : f 154 = f (f (154 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₀₁]
    have h₁₈₀₂ : f (154 + 5) = f 159 := by norm_num
    rw [h₁₈₀₂]
    rw [h₁₇₉]
    <;> norm_num
    <;> linarith
  
  have h₁₈₁ : f 149 = 998 := by
    have h₁₈₁₁ : f 149 = f (f (149 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₁₁]
    have h₁₈₁₂ : f (149 + 5) = f 154 := by norm_num
    rw [h₁₈₁₂]
    rw [h₁₈₀]
    <;> norm_num
    <;> linarith
  
  have h₁₈₂ : f 144 = 997 := by
    have h₁₈₂₁ : f 144 = f (f (144 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₂₁]
    have h₁₈₂₂ : f (144 + 5) = f 149 := by norm_num
    rw [h₁₈₂₂]
    rw [h₁₈₁]
    <;> norm_num
    <;> linarith
  
  have h₁₈₃ : f 139 = 998 := by
    have h₁₈₃₁ : f 139 = f (f (139 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₃₁]
    have h₁₈₃₂ : f (139 + 5) = f 144 := by norm_num
    rw [h₁₈₃₂]
    rw [h₁₈₂]
    <;> norm_num
    <;> linarith
  
  have h₁₈₄ : f 134 = 997 := by
    have h₁₈₄₁ : f 134 = f (f (134 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₄₁]
    have h₁₈₄₂ : f (134 + 5) = f 139 := by norm_num
    rw [h₁₈₄₂]
    rw [h₁₈₃]
    <;> norm_num
    <;> linarith
  
  have h₁₈₅ : f 129 = 998 := by
    have h₁₈₅₁ : f 129 = f (f (129 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₅₁]
    have h₁₈₅₂ : f (129 + 5) = f 134 := by norm_num
    rw [h₁₈₅₂]
    rw [h₁₈₄]
    <;> norm_num
    <;> linarith
  
  have h₁₈₆ : f 124 = 997 := by
    have h₁₈₆₁ : f 124 = f (f (124 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₆₁]
    have h₁₈₆₂ : f (124 + 5) = f 129 := by norm_num
    rw [h₁₈₆₂]
    rw [h₁₈₅]
    <;> norm_num
    <;> linarith
  
  have h₁₈₇ : f 119 = 998 := by
    have h₁₈₇₁ : f 119 = f (f (119 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₇₁]
    have h₁₈₇₂ : f (119 + 5) = f 124 := by norm_num
    rw [h₁₈₇₂]
    rw [h₁₈₆]
    <;> norm_num
    <;> linarith
  
  have h₁₈₈ : f 114 = 997 := by
    have h₁₈₈₁ : f 114 = f (f (114 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₈₁]
    have h₁₈₈₂ : f (114 + 5) = f 119 := by norm_num
    rw [h₁₈₈₂]
    rw [h₁₈₇]
    <;> norm_num
    <;> linarith
  
  have h₁₈₉ : f 109 = 998 := by
    have h₁₈₉₁ : f 109 = f (f (109 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₈₉₁]
    have h₁₈₉₂ : f (109 + 5) = f 114 := by norm_num
    rw [h₁₈₉₂]
    rw [h₁₈₈]
    <;> norm_num
    <;> linarith
  
  have h₁₉₀ : f 104 = 997 := by
    have h₁₉₀₁ : f 104 = f (f (104 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₉₀₁]
    have h₁₉₀₂ : f (104 + 5) = f 109 := by norm_num
    rw [h₁₉₀₂]
    rw [h₁₈₉]
    <;> norm_num
    <;> linarith
  
  have h₁₉₁ : f 99 = 998 := by
    have h₁₉₁₁ : f 99 = f (f (99 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₉₁₁]
    have h₁₉₁₂ : f (99 + 5) = f 104 := by norm_num
    rw [h₁₉₁₂]
    rw [h₁₉₀]
    <;> norm_num
    <;> linarith
  
  have h₁₉₂ : f 94 = 997 := by
    have h₁₉₂₁ : f 94 = f (f (94 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₉₂₁]
    have h₁₉₂₂ : f (94 + 5) = f 99 := by norm_num
    rw [h₁₉₂₂]
    rw [h₁₉₁]
    <;> norm_num
    <;> linarith
  
  have h₁₉₃ : f 89 = 998 := by
    have h₁₉₃₁ : f 89 = f (f (89 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₉₃₁]
    have h₁₉₃₂ : f (89 + 5) = f 94 := by norm_num
    rw [h₁₉₃₂]
    rw [h₁₉₂]
    <;> norm_num
    <;> linarith
  
  have h₁₉₄ : f 84 = 997 := by
    have h₁₉₄₁ : f 84 = f (f (84 + 5)) := by
      apply h₁
      <;> norm_num
    rw [h₁₉₄₁]
    have h₁₉₄₂ : f (84 + 5) = f 89 := by norm_num
    rw [h₁₉₄₂]
    rw [h₁₉₃]
    <;> norm_num
    <;> linarith
  
  rw [h₁₉₄]
  <;> norm_num