module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceLocalSpectrum

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- A radius budget for the two harmonic features bounds every local length,
without a restriction on the arc or the lag. -/
theorem localDistanceModel_le_three_radius (R θ b₁ b₂ δ d : ℝ)
    (hR : 0 ≤ R) (hbudget : b₁ ^ 2 + b₂ ^ 2 ≤ R ^ 2) :
    localDistanceModel R θ b₁ b₂ δ d ≤ 3 * R := by
  have hc₀ := Real.sin_sq_le_one (d / (2 * R))
  have hc := mul_le_mul_of_nonneg_left hc₀ (show 0 ≤ 4 * R ^ 2 by positivity)
  have hc' : (circleChord R d) ^ 2 ≤ 4 * R ^ 2 := by
    unfold circleChord
    nlinarith only [hc]
  have he₀ := Real.sin_sq_le_one (θ * δ / 2)
  have he₁ := Real.sin_sq_le_one (θ * δ)
  have he₀' := mul_le_mul_of_nonneg_left he₀ (show 0 ≤ 4 * b₁ ^ 2 by positivity)
  have he₁' := mul_le_mul_of_nonneg_left he₁ (show 0 ≤ 4 * b₂ ^ 2 by positivity)
  have he : harmonicEnergy θ b₁ b₂ δ ≤ 4 * (b₁ ^ 2 + b₂ ^ 2) := by
    unfold harmonicEnergy
    nlinarith only [he₀', he₁']
  have hs := localDistanceModel_square R θ b₁ b₂ δ d
  have hpos := localDistanceModel_nonneg R θ b₁ b₂ δ d
  nlinarith [sq_nonneg R]

theorem sourceOffset_ge_fivehundred_m (m : ℕ) (hm : 34000 ≤ m) :
    (500 : ℝ) * m ≤ sourceOffset m := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) ≤ m := by positivity
  have hceil := Nat.le_ceil ((m : ℝ) * ((m : ℝ) - 1) / 64)
  change (m : ℝ) * ((m : ℝ) - 1) / 64 ≤ (sourceOffset m : ℝ) at hceil
  have hmul := mul_nonneg hm₀ (show (0 : ℝ) ≤ m - 34000 by linarith)
  nlinarith

theorem sourceRadius_le_onehundredthirtythree (m k : ℕ) :
    sourceRadius m k ≤ 133 * (m : ℝ) * (k : ℝ) ^ 2 := by
  have hR : 0 ≤ sourceRadius m k := by unfold sourceRadius; positivity
  have hsq := sourceRadius_square m k
  let t : ℝ := (m : ℝ) * (k : ℝ) ^ 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsq' : (sourceRadius m k) ^ 2 = 17500 * t ^ 2 := by
    dsimp [t]
    nlinarith only [hsq]
  calc
    sourceRadius m k ≤ 133 * t := by nlinarith [sq_nonneg t]
    _ = 133 * (m : ℝ) * (k : ℝ) ^ 2 := by dsimp [t]; ring

theorem source_mixed_scalar_budget (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    3 * sourceRadius m k + 1 ≤
      sourceTmin (sourceOffset m) k - sourceError (sourceOffset m) k := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK := sourceOffset_ge_fivehundred_m m hm
  have hKfixed := sourceOffset_lower m hm
  have hmul := mul_le_mul_of_nonneg_left hK (sq_nonneg (k : ℝ))
  have hbase : 700 * (m : ℝ) * (k : ℝ) ^ 2 ≤
      sourceBaseline (sourceOffset m) k := by
    unfold sourceBaseline sourceMacroStep
    nlinarith [hmul]
  have hpert := source_perturbation_quadratic_bound (k : ℝ) hk'
  have herr := source_error_linear_bound (sourceOffset m) k hKfixed hk'
  have hmK := mul_le_mul_of_nonneg_right hm' (sq_nonneg (k : ℝ))
  have hk₂ : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hT : 600 * (m : ℝ) * (k : ℝ) ^ 2 ≤
      sourceTmin (sourceOffset m) k - sourceError (sourceOffset m) k := by
    unfold sourceTmin
    nlinarith
  have hR := sourceRadius_le_onehundredthirtythree m k
  have hmk : 1 ≤ (m : ℝ) * (k : ℝ) ^ 2 := by nlinarith [hmK]
  nlinarith

/-- The actual source cross distance lies above every local distance once the
local harmonic reserves fit inside the common radius budget. -/
theorem source_local_cross_gap (D b₁ b₂ : ℝ) (p m k A l δ a i j : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hi : i < k) (hj : j < k)
    (hD : 0 ≤ D)
    (hsq : D ^ 2 =
      (sourceCrossBaseline (sourceOffset m) k a + sourceAlpha k i + sourceBeta k j) ^ 2 -
        2 * sourceAlpha k i * sourceBeta k j)
    (hbudget : b₁ ^ 2 + b₂ ^ 2 ≤ (sourceRadius m k) ^ 2) :
    1 ≤ D - sourceLocalDistance p m k b₁ b₂ A l δ := by
  have hK := sourceOffset_lower m hm
  have herr := source_cross_error D (sourceOffset m) k a i j hK hk hi hj hD hsq
  have hpert := source_digit_sum_bound k i j hk hi hj
  have hbase : sourceBaseline (sourceOffset m) k ≤
      sourceCrossBaseline (sourceOffset m) k a := by
    have hnonneg : 0 ≤ sourceMacroStep k * (a : ℝ) := by
      unfold sourceMacroStep
      positivity
    unfold sourceCrossBaseline
    linarith
  have hcross : sourceTmin (sourceOffset m) k - sourceError (sourceOffset m) k ≤ D := by
    have he := (abs_le.mp herr).1
    have hp := (abs_le.mp hpert).1
    unfold sourceTmin at *
    linarith
  have hR : 0 ≤ sourceRadius m k := by unfold sourceRadius; positivity
  have hlocal : sourceLocalDistance p m k b₁ b₂ A l δ ≤ 3 * sourceRadius m k := by
    unfold sourceLocalDistance
    exact localDistanceModel_le_three_radius _ _ _ _ _ _ hR hbudget
  linarith [source_mixed_scalar_budget m k hm hk]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
