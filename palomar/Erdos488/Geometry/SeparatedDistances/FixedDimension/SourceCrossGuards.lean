module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SineDigits
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.DirectCrossSpectrum

@[expose] public section

/-! Universal source-parameter cross guards, not finite sampled certificates.
The hypotheses are k≥2 and K≥72247875/4, with the literal source formulas. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sourceMacroStep (k : ℝ) : ℝ := (9/8 : ℝ)^3*k^2
noncomputable def sourcePerturbationBound (k : ℝ) : ℝ := (9/8 : ℝ)*((9/8 : ℝ)*k+1)*((k-1)/2)
noncomputable def sourceBaseline (K k : ℝ) : ℝ := sourceMacroStep k*(K+1)
noncomputable def sourceTmin (K k : ℝ) : ℝ := sourceBaseline K k-sourcePerturbationBound k
noncomputable def sourceError (K k : ℝ) : ℝ := 2*(9/8 : ℝ)^3*k^3/sourceTmin K k

theorem source_perturbation_quadratic_bound (k : ℝ) (hk : 2 ≤ k) :
    sourcePerturbationBound k ≤ (117/128 : ℝ)*k^2 := by
  unfold sourcePerturbationBound
  nlinarith [sq_nonneg k]

theorem source_baseline_lower (K k : ℝ) (hK : 72247875/4 ≤ K) :
    (52668703791/2048 : ℝ)*k^2 ≤ sourceBaseline K k := by
  have h := mul_le_mul_of_nonneg_left hK (show 0 ≤ (9/8 : ℝ)^3*k^2 by positivity)
  unfold sourceBaseline sourceMacroStep
  nlinarith

theorem source_Tmin_lower (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    (52668701919/2048 : ℝ)*k^2 ≤ sourceTmin K k := by
  have h₀ := source_baseline_lower K k hK
  have h₁ := source_perturbation_quadratic_bound k hk
  unfold sourceTmin
  linarith

theorem source_Tmin_pos (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    0 < sourceTmin K k := by
  have h := source_Tmin_lower K k hK hk
  nlinarith [sq_nonneg (k-2)]

/-- The pointwise error is at most k times one exact rational, uniformly in K,k. -/
theorem source_error_linear_bound (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    sourceError K k ≤ (648/5852077991 : ℝ)*k := by
  have hT := source_Tmin_lower K k hK hk
  have hTpos := source_Tmin_pos K k hK hk
  have hm := mul_le_mul_of_nonneg_left hT (show 0 ≤ (648/5852077991 : ℝ)*k by positivity)
  unfold sourceError
  apply (div_le_iff₀ hTpos).2
  nlinarith

/-- Every direct polarization fine guard, in denominator-cleared form. -/
theorem source_direct_fine_guard (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    sourceBaseline K k+sourcePerturbationBound k+sourceError K k ≤
      ((9/8 : ℝ)*(255/256))*(sourceBaseline K k-(9/8)*((k-1)/2)) := by
  have hν := source_baseline_lower K k hK
  have hA := source_perturbation_quadratic_bound k hk
  have hE := source_error_linear_bound K k hK hk
  have hk₂ : 2*k ≤ k^2 := by nlinarith
  nlinarith

theorem source_direct_carry_guard (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    1 ≤ (9/8 : ℝ)*(((9/8)*k)*(255/256)-2*((k-1)/2))-2*sourceError K k := by
  have hE := source_error_linear_bound K k hK hk
  nlinarith

theorem source_direct_macro_guard (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    1 ≤ sourceMacroStep k-2*sourcePerturbationBound k-2*sourceError K k := by
  have hE := source_error_linear_bound K k hK hk
  unfold sourceMacroStep sourcePerturbationBound
  nlinarith [sq_nonneg k]

theorem source_baseline_exceeds_fine_bound (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    (9/8 : ℝ)*((k-1)/2) ≤ sourceBaseline K k := by
  have hν := source_baseline_lower K k hK
  nlinarith [sq_nonneg (k-2)]

/-- Actual ceiling offset from the candidate, with its universal macro-size bound. -/
noncomputable def sourceOffset (m : ℕ) : ℕ := ⌈(m : ℝ)*((m : ℝ)-1)/64⌉₊

theorem sourceOffset_lower (m : ℕ) (hm : 34000 ≤ m) :
    (72247875/4 : ℝ) ≤ sourceOffset m := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have h := Nat.le_ceil ((m : ℝ)*((m : ℝ)-1)/64)
  change (72247875/4 : ℝ) ≤ (⌈(m : ℝ)*((m : ℝ)-1)/64⌉₊ : ℝ)
  nlinarith [sq_nonneg ((m : ℝ)-34000)]

/-- The nominal lower bound remains positive after the actual pointwise error. -/
theorem source_error_lt_Tmin (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    sourceError K k < sourceTmin K k := by
  have ht := source_Tmin_lower K k hK hk
  have he := source_error_linear_bound K k hK hk
  nlinarith [sq_nonneg (k-2)]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
