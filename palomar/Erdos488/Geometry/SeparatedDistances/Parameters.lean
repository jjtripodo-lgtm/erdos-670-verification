module

public import Erdos488.Geometry.SeparatedDistances.Defs
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

/-- The seed size in the explicit square-root-logarithmic construction. -/
noncomputable def seedSize (n : ℕ) : ℕ :=
  max 50000 ⌈Real.sqrt (5000 * (harmonic n : ℝ))⌉₊

theorem seedSize_ge_50000 (n : ℕ) : 50000 ≤ seedSize n := by
  unfold seedSize
  exact Nat.le_max_left _ _

theorem seedSize_ge_three (n : ℕ) : 3 ≤ seedSize n := by
  exact (by norm_num : 3 ≤ 50000).trans (seedSize_ge_50000 n)

theorem seedSize_square_ge_harmonic (n : ℕ) :
    5000 * (harmonic n : ℝ) ≤ (seedSize n : ℝ) ^ 2 := by
  have hHq : (0 : ℚ) ≤ harmonic n := by
    unfold harmonic
    positivity
  have hH : (0 : ℝ) ≤ (harmonic n : ℝ) := by exact_mod_cast hHq
  have hx : 0 ≤ 5000 * (harmonic n : ℝ) := mul_nonneg (by norm_num) hH
  have hsqrtR : Real.sqrt (5000 * (harmonic n : ℝ)) ≤ (seedSize n : ℝ) := by
    calc
      _ ≤ (⌈Real.sqrt (5000 * (harmonic n : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (seedSize n : ℝ) := by
        exact_mod_cast (show ⌈Real.sqrt (5000 * (harmonic n : ℝ))⌉₊ ≤ seedSize n by
        unfold seedSize
        exact Nat.le_max_right _ _)
  calc
    _ = Real.sqrt (5000 * (harmonic n : ℝ)) ^ 2 := (Real.sq_sqrt hx).symm
    _ ≤ (seedSize n : ℝ) ^ 2 := by
      have hmul := mul_self_le_mul_self (Real.sqrt_nonneg _) hsqrtR
      simpa [pow_two] using hmul

/-- The elementary bound on harmonic numbers used for the parameter range. -/
theorem harmonic_le_nat (n : ℕ) : harmonic n ≤ n := by
  unfold harmonic
  calc
    ∑ i ∈ Finset.range n, (↑(i + 1) : ℚ)⁻¹
        ≤ ∑ _i ∈ Finset.range n, (1 : ℚ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact inv_le_one_of_one_le₀ (by norm_num)
    _ = n := by simp

theorem harmonic_le_seventeen_of_le_50000 {n : ℕ} (hn : n ≤ 50000) :
    (harmonic n : ℝ) ≤ 17 := by
  by_cases hn0 : n = 0
  · subst n
    simp [harmonic]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hn65536 : n ≤ 2 ^ 16 := by norm_num; omega
  have hlog : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ 16) := by
    rw [Real.log_le_log_iff (by positivity) (by positivity)]
    exact_mod_cast hn65536
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hh := harmonic_le_one_add_log n
  rw [Real.log_pow] at hlog
  norm_num at hlog
  nlinarith

/-- The coarse quadratic inequality sufficient to fit the seed inside the vertex set. -/
theorem parameter_square_dominates {n : ℕ} (hn : 50001 ≤ n) :
    5000 * n ≤ (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : 50001 + m - 1 = 50000 + m := by omega
  rw [hsub]
  calc
    5000 * (50001 + m)
        ≤ 5000 * (50001 + m) + (m ^ 2 + 95000 * m + 2249995000) :=
          Nat.le_add_right _ _
    _ = (50000 + m) ^ 2 := by ring

/-- For the large-`n` branch, the chosen seed has at most `n-1` vertices. -/
theorem seedSize_le_pred {n : ℕ} (hn : 50001 ≤ n) : seedSize n ≤ n - 1 := by
  rw [seedSize, max_le_iff]
  constructor
  · omega
  · rw [Nat.ceil_le]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hhq := harmonic_le_nat n
      have hh : (harmonic n : ℝ) ≤ n := by exact_mod_cast hhq
      have hsquare := parameter_square_dominates hn
      exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans (by exact_mod_cast hsquare)

end Erdos488.Geometry.SeparatedDistances
