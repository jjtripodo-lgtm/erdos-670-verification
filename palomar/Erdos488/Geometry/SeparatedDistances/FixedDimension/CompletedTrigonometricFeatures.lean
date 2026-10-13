module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletionFactor
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.TrigonometricFeatures

@[expose] public section

/-! Exact global factor-to-coordinate feature identities, following C1--C3.
The matrix factor equality is supplied by the independent global PSD construction. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

theorem diagonal_bilinear_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w x y : κ → ℝ) :
    x ⬝ᵥ ((Matrix.diagonal w) *ᵥ y) = ∑ q, w q*x q*y q := by
  simp only [Matrix.mulVec_diagonal,dotProduct,Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Off-cluster cancellation for the actual embedded five-coordinate features. -/
theorem completed_feature_cross_cancel {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w : ℝ) :
    (M *ᵥ clusteredFeature A z) ⬝ᵥ (M *ᵥ clusteredFeature B w)+
      (V *ᵥ clusteredFeature A z) ⬝ᵥ (V *ᵥ clusteredFeature B w)=0 := by
  rw [completed_bilinear_identity M V _ hfactor,diagonal_bilinear_sum,
    clusteredFeature_weighted_dot,if_neg hAB]

/-- The completed macro-plus-residual perturbation has the exact common norm. -/
theorem completed_feature_constant_norm {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A : Fin m) (z : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q)^2)=b₀^2+b₁^2+b₂^2 := by
  have h := completed_bilinear_identity M V _ hfactor (clusteredFeature A z) (clusteredFeature A z)
  rw [diagonal_bilinear_sum] at h
  simp_rw [dotProduct,mul_assoc,← sq] at h
  exact h.trans (clusteredFeature_constant_norm A b₀ b₁ b₂ z)

/-- The actual completed coordinates have precisely the claimed same-cluster harmonics. -/
theorem completed_feature_difference_square {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A : Fin m) (z w : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q-(M *ᵥ clusteredFeature A w) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q-(V *ᵥ clusteredFeature A w) q)^2)=
      (2*b₁*Real.sin ((z-w)/2))^2+(2*b₂*Real.sin (z-w))^2 := by
  have h := completed_bilinear_identity M V _ hfactor
    (clusteredFeature A z-clusteredFeature A w) (clusteredFeature A z-clusteredFeature A w)
  rw [diagonal_bilinear_sum] at h
  simp_rw [Matrix.mulVec_sub,Pi.sub_apply,dotProduct,mul_assoc,← sq] at h
  exact h.trans (clusteredFeature_difference_square A b₀ b₁ b₂ z w)

/-- The private circle and constant axis turn the common feature reserve into 2R².
The nonnegative square-root reserve is a genuine explicit requirement. -/
theorem completed_full_perturbation_norm {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ R : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (hreserve : b₀^2+b₁^2+b₂^2 ≤ R^2) (A : Fin m) (z angle : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q)^2)+
      (R*Real.cos angle)^2+(R*Real.sin angle)^2+
      (Real.sqrt (R^2-(b₀^2+b₁^2+b₂^2)))^2=2*R^2 := by
  rw [completed_feature_constant_norm M V b₀ b₁ b₂ hfactor A z]
  rw [Real.sq_sqrt (sub_nonneg.mpr hreserve)]
  have h := congrArg (fun x : ℝ => R^2*x) (Real.sin_sq_add_cos_sq angle)
  nlinarith only [h]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
