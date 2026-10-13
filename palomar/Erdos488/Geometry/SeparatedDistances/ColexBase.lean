module

public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

/-- The elementary two-coordinate inequality used at the start of the colex path form. -/
theorem two_coordinate_path_bound (s t : ℝ) :
    (s - t) ^ 2 + s ^ 2 ≥ (s ^ 2 + t ^ 2) / 3 := by
  nlinarith [sq_nonneg (2 * s - t)]

/-- The first two colex coordinates retain the manuscript's `K²/24` weight. -/
theorem colex_first_two_coercivity {K s t : ℝ} (hK : 10 ≤ K) :
    K ^ 2 / 4 * (s - t) ^ 2 + K ^ 2 / 4 * s ^ 2 - 4 * t ^ 2 ≥
      K ^ 2 / 24 * (s ^ 2 + t ^ 2) := by
  have hbase := two_coordinate_path_bound s t
  have hk96 : 96 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 10)]
  nlinarith [mul_le_mul_of_nonneg_left hbase (sq_nonneg K),
    mul_nonneg (sub_nonneg.mpr hk96) (sq_nonneg t)]

/-- Interior colex potential bound at index three. -/
theorem colex_potential_three {K : ℝ} (hK : 3 ≤ K) :
    K - 3 / 2 ≥ (3 * K + 27) / 24 := by
  linarith

/-- Interior colex potential bound for every real index at least four. -/
theorem colex_potential_ge_four {K i : ℝ} (hK : 10 ≤ K) (hi : 4 ≤ i) :
    (i - 2) * K + i / 2 * (i ^ 2 - 2 * i - 4) ≥
      (K * i + i ^ 3) / 24 := by
  nlinarith [sq_nonneg (i - 2)]

end Erdos488.Geometry.SeparatedDistances
