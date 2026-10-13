module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceCrossGuards
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanCrossCoordinates

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sourceDigit (k i : ℕ) : ℝ :=
  sineDigit (Real.sqrt (1/32)/(k : ℝ)) (((k : ℝ)-1)/2) i
noncomputable def sourceCrossBaseline (K : ℝ) (k a : ℕ) : ℝ :=
  sourceBaseline K k+sourceMacroStep k*a
noncomputable def sourceAlpha (k i : ℕ) : ℝ := (9/8 : ℝ)*((9/8)*(k : ℝ))*sourceDigit k i
noncomputable def sourceBeta (k i : ℕ) : ℝ := (9/8 : ℝ)*sourceDigit k i

theorem sourceDigit_bound (k i : ℕ) (hk : 2 ≤ k) (hi : i < k) :
    |sourceDigit k i| ≤ ((k : ℝ)-1)/2 := by
  apply finite_sineDigit_bound
  · have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  · exact hi

theorem sourceDigit_step (k i : ℕ) (hk : 2 ≤ k) (hi : i+1 < k) :
    (255 : ℝ)/256 ≤ sourceDigit k (i+1)-sourceDigit k i := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h := finite_sineDigit_source_step (Real.sqrt (1/32)/(k : ℝ)) k i
    (by positivity) hi (source_theta_scale k (by omega)).le
  simpa only [sourceDigit,Nat.cast_add,Nat.cast_one] using h

theorem source_digit_sum_bound (k i j : ℕ) (hk : 2 ≤ k) (hi : i < k) (hj : j < k) :
    |sourceAlpha k i+sourceBeta k j| ≤ sourcePerturbationBound k := by
  obtain ⟨hli,hui⟩ := abs_le.mp (sourceDigit_bound k i hk hi)
  obtain ⟨hlj,huj⟩ := abs_le.mp (sourceDigit_bound k j hk hj)
  have hk' : (0 : ℝ) ≤ k := by positivity
  have hi₀ := mul_le_mul_of_nonneg_left hli hk'
  have hi₁ := mul_le_mul_of_nonneg_left hui hk'
  unfold sourceAlpha sourceBeta sourcePerturbationBound
  apply abs_le.mpr
  constructor <;> nlinarith

theorem source_digit_product_bound (k i j : ℕ) (hk : 2 ≤ k) (hi : i < k) (hj : j < k) :
    |sourceAlpha k i*sourceBeta k j| ≤ (9/8 : ℝ)^3*(k : ℝ)^3 := by
  have hfi := sourceDigit_bound k i hk hi
  have hfj := sourceDigit_bound k j hk hj
  have hk' : (0 : ℝ) ≤ k := by positivity
  have hi' : |sourceDigit k i| ≤ (k : ℝ) := by linarith
  have hj' : |sourceDigit k j| ≤ (k : ℝ) := by linarith
  have hp := mul_le_mul hi' hj' (abs_nonneg _) hk'
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (9/8 : ℝ)^3*(k : ℝ) by positivity)
  have he : |sourceAlpha k i*sourceBeta k j|=
      (9/8 : ℝ)^3*(k : ℝ)*(|sourceDigit k i| * |sourceDigit k j|) := by
    unfold sourceAlpha sourceBeta
    rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_mul]
    simp only [abs_of_nonneg hk']
    norm_num
    ring
  rw [he]
  nlinarith

/-- Pointwise errors for the literal source digits, without assuming an error bound. -/
theorem source_cross_error (D K : ℝ) (k a i j : ℕ) (hK : 72247875/4 ≤ K)
    (hk : 2 ≤ k) (hi : i < k) (hj : j < k) (hD : 0 ≤ D)
    (hsq : D^2=(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)^2-
      2*sourceAlpha k i*sourceBeta k j) :
    |D-(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)| ≤ sourceError K k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : sourceBaseline K k ≤ sourceCrossBaseline K k a := by
    have h : 0 ≤ sourceMacroStep k*(a : ℝ) := by unfold sourceMacroStep; positivity
    unfold sourceCrossBaseline
    linarith
  have hpert := (abs_le.mp (source_digit_sum_bound k i j hk hi hj)).1
  have hu : sourceTmin K k ≤ sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j := by
    unfold sourceTmin
    linarith
  simpa only [sourceError,mul_assoc] using cross_error_uniform_bound D _ (sourceAlpha k i) (sourceBeta k j)
    ((9/8 : ℝ)^3*(k : ℝ)^3) (sourceTmin K k) hD (source_Tmin_pos K k hK hk') hu
    (source_digit_product_bound k i j hk hi hj) hsq

/-- Complete source-specific cross-spectrum separation. The only metric inputs
are nonnegativity and the corrected exact squared-distance formula. All sine,
pointwise-error, fine, carry and macro guards are proved, uniformly in k,K. -/
theorem source_cross_spectrum_separated (D : ℕ → ℕ → ℕ → ℝ) (M k : ℕ) (K : ℝ)
    (hk : 2 ≤ k) (hK : 72247875/4 ≤ K)
    (hD : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 ≤ D a i j)
    (hsq : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      (D a i j)^2=(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)^2-
        2*sourceAlpha k i*sourceBeta k j) :
    ∀ a i j b u v, a < M → i < k → j < k → b < M → u < k → v < k →
      (a,i,j) ≠ (b,u,v) → 1 ≤ |D a i j-D b u v| := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hν (a : ℕ) : sourceBaseline K k ≤ sourceCrossBaseline K k a := by
    have h : 0 ≤ sourceMacroStep k*(a : ℝ) := by unfold sourceMacroStep; positivity
    unfold sourceCrossBaseline
    linarith
  have herr : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      |D a i j-(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)| ≤ sourceError K k := by
    intro a ha i hi j hj
    exact source_cross_error (D a i j) K k a i j hK hk hi hj (hD a ha i hi j hj)
      (hsq a ha i hi j hj)
  have hpos : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 < D a i j := by
    intro a ha i hi j hj
    have he := (abs_le.mp (herr a ha i hi j hj)).1
    have hu := (abs_le.mp (source_digit_sum_bound k i j hk hi hj)).1
    have hb := hν a
    have ht := source_error_lt_Tmin K k hK hk'
    unfold sourceTmin at ht
    linarith
  have hbase : ∀ a, a+1 < M → sourceMacroStep k ≤
      sourceCrossBaseline K k (a+1)-sourceCrossBaseline K k a := by
    intro a _
    simp only [sourceCrossBaseline,Nat.cast_add,Nat.cast_one]
    linarith
  exact direct_cross_spectrum_separated D (sourceCrossBaseline K k) (sourceDigit k) M k (by omega)
    (9/8) ((9/8)*(k : ℝ)) (255/256) (((k : ℝ)-1)/2)
    (sourceError K k) (sourceMacroStep k) (sourceBaseline K k)
    (by norm_num) (by positivity) (fun a _ => hν a)
    (source_baseline_exceeds_fine_bound K k hK hk')
    (fun i hi => sourceDigit_bound k i hk hi) (fun i hi => sourceDigit_step k i hk hi)
    hbase hpos hsq herr (by norm_num)
    (by simpa only [sourcePerturbationBound] using source_direct_fine_guard K k hK hk')
    (source_direct_carry_guard K k hK hk')
    (by simpa only [sourcePerturbationBound] using source_direct_macro_guard K k hK hk')

/-- The source's actual ceiling choice now discharges the macro-size premise. -/
theorem source_offset_cross_spectrum_separated (D : ℕ → ℕ → ℕ → ℝ) (M m k : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k)
    (hD : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 ≤ D a i j)
    (hsq : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      (D a i j)^2=(sourceCrossBaseline (sourceOffset m) k a+sourceAlpha k i+sourceBeta k j)^2-
        2*sourceAlpha k i*sourceBeta k j) :
    ∀ a i j b u v, a < M → i < k → j < k → b < M → u < k → v < k →
      (a,i,j) ≠ (b,u,v) → 1 ≤ |D a i j-D b u v| := by
  exact source_cross_spectrum_separated D M k (sourceOffset m) hk (sourceOffset_lower m hm) hD hsq

end Erdos488.Geometry.SeparatedDistances.FixedDimension
