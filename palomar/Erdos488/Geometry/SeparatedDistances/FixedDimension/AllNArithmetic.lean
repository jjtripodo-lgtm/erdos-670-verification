module

public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Every sufficiently large requested size is contained in a rectangular
cluster size with a bounded number of clusters. This closes only the integer
rounding step of PR 2974; configuration existence is not a premise or conclusion. -/
theorem every_large_n_cluster_parameters (n : ℕ) (hn : 68000 ≤ n) :
    ∃ k m : ℕ, 2 ≤ k ∧ 34000 ≤ m ∧ m ≤ 51000 ∧
      n ≤ m*k ∧ m*k < n+k ∧ 34000*k ≤ n := by
  let k := n / 34000
  let r := n % 34000
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hk0 : 0 < k := by omega
  have hr : r < 34000 := Nat.mod_lt _ (by norm_num)
  have hnkr : 34000*k+r = n := Nat.div_add_mod n 34000
  have hsub : r+k-1+1 = r+k := by omega
  let q := (r+k-1)/k
  have hqUpper : q ≤ 17000 := by
    have hnum : r+k-1 < (17000+1)*k := by omega
    have := (Nat.div_lt_iff_lt_mul hk0).2 hnum
    change q < 17001 at this
    omega
  have hqmul : q*k ≤ r+k-1 := Nat.div_mul_le_self _ _
  have hnext : r+k-1 < (q+1)*k := by
    simpa [q, Nat.mul_comm] using Nat.lt_mul_div_succ (r+k-1) hk0
  refine ⟨k, 34000+q, hk, Nat.le_add_right _ _, by linarith, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · omega

end Erdos488.Geometry.SeparatedDistances.FixedDimension
