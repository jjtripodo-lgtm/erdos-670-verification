module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanClusterCoordinates

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

/-- Exact finite sum identity used to expand Euclidean squared distances. -/
theorem sum_sq_sub {κ : Type*} [Fintype κ] (x y : κ → ℝ) :
    (∑ q, (x q-y q)^2)=(∑ q, (x q)^2)+(∑ q, (y q)^2)-2*(x ⬝ᵥ y) := by
  have he : ∀ q, (x q-y q)^2=(x q)^2+(y q)^2-2*(x q*y q) := by
    intro q
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,dotProduct,← Finset.mul_sum]

/-- Squared feature distance across distinct clusters is twice the reserve. -/
theorem completed_cross_feature_square {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q-(M *ᵥ clusteredFeature B w) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q-(V *ᵥ clusteredFeature B w) q)^2)=
        2*(b₀^2+b₁^2+b₂^2) := by
  rw [sum_sq_sub,sum_sq_sub]
  have h₀ := completed_feature_constant_norm M V b₀ b₁ b₂ hfactor A z
  have h₁ := completed_feature_constant_norm M V b₀ b₁ b₂ hfactor B w
  have hcross := completed_feature_cross_cancel M V b₀ b₁ b₂ hfactor A B hAB z w
  linarith

theorem privateCircle_norm_square {m : ℕ} (A : Fin m) (R y : ℝ) :
    (∑ q, (privateCircle A R y q)^2)=R^2 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ B : Fin m, (∑ a : Fin 2, (privateCircle A R y (B,a))^2)=
      if B=A then (R*Real.cos (y/R))^2+(R*Real.sin (y/R))^2 else 0 := by
    intro B
    by_cases h : B=A <;> simp [privateCircle,h,Fin.sum_univ_succ]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have h := congrArg (fun x : ℝ => R^2*x) (Real.sin_sq_add_cos_sq (y/R))
  nlinarith only [h]

theorem privateCircle_cross_dot {m : ℕ} (A B : Fin m) (hAB : A ≠ B) (R yj yi : ℝ) :
    privateCircle A R yj ⬝ᵥ privateCircle B R yi=0 := by
  apply Finset.sum_eq_zero
  intro q _
  by_cases h : q.1=A
  · have h' : q.1 ≠ B := by simpa [h] using hAB
    simp [privateCircle,h,hAB]
  · simp [privateCircle,h]

theorem privateCircle_cross_square {m : ℕ} (A B : Fin m) (hAB : A ≠ B) (R yj yi : ℝ) :
    (∑ q, (privateCircle A R yj q-privateCircle B R yi q)^2)=2*R^2 := by
  rw [sum_sq_sub,privateCircle_norm_square,privateCircle_norm_square,
    privateCircle_cross_dot A B hAB]
  ring

theorem privateAxis_cross_square {m : ℕ} (A B : Fin m) (hAB : A ≠ B) (axis : ℝ) :
    (∑ C : Fin m, ((if C=A then axis else 0)-(if C=B then axis else 0))^2)=2*axis^2 := by
  have he : ∀ C : Fin m, ((if C=A then axis else 0)-(if C=B then axis else 0))^2=
      (if C=A then axis^2 else 0)+(if C=B then axis^2 else 0) := by
    intro C
    by_cases ha : C=A
    · have hb : C ≠ B := by simpa [ha] using hAB
      simp [ha,hb,hAB,Ne.symm hAB]
    · by_cases hb : C=B <;> simp [ha,hb,hAB,Ne.symm hAB]
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  ring

/-- General macro-coordinate expansion, with both signed projection terms retained. -/
theorem macro_coordinate_expansion {ι : Type*} [Fintype ι] (a b u v : ι → ℝ) (S : ℝ) :
    (∑ q, (S*a q+u q-(S*b q+v q))^2)=
      S^2*(∑ q, (a q-b q)^2)+2*S*((a-b) ⬝ᵥ (u-v))+(∑ q, (u q-v q)^2) := by
  have he : ∀ q, (S*a q+u q-(S*b q+v q))^2=
      S^2*(a q-b q)^2+2*S*((a q-b q)*(u q-v q))+(u q-v q)^2 := by
    intro q
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,dotProduct,Pi.sub_apply]

/-- The actual cross-cluster Euclidean square, before imposing projection targets. -/
theorem clusterPoint_cross_square {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w yj yi : ℝ) :
    dist (clusterPoint centers M V S R axis A z yj)
      (clusterPoint centers M V S R axis B w yi)^2=
      S^2*(∑ q, (centers A q-centers B q)^2)+
      2*S*((centers A-centers B) ⬝ᵥ
        ((M *ᵥ clusteredFeature A z)-(M *ᵥ clusteredFeature B w)))+
      2*(R^2+axis^2+b₀^2+b₁^2+b₂^2) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [clusterPoint,WithLp.ofLp_toLp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Real.dist_eq,sq_abs]
  rw [macro_coordinate_expansion,privateCircle_cross_square A B hAB,
    privateAxis_cross_square A B hAB]
  have h := completed_cross_feature_square M V b₀ b₁ b₂ hfactor A B hAB z w
  linarith

/-- The exact cross metric now follows from actual Euclidean coordinates and
both directed projection equations; the mixed product is retained. -/
theorem clusterPoint_cross_metric_square {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis b₀ b₁ b₂ ν α β : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w yj yi : ℝ)
    (haxis : axis^2=R^2-(b₀^2+b₁^2+b₂^2))
    (hbase : S^2*(∑ q, (centers A q-centers B q)^2)+4*R^2=ν^2)
    (hprojA : 2*S*((centers A-centers B) ⬝ᵥ (M *ᵥ clusteredFeature A z))=2*ν*α+α^2)
    (hprojB : -2*S*((centers A-centers B) ⬝ᵥ (M *ᵥ clusteredFeature B w))=2*ν*β+β^2) :
    dist (clusterPoint centers M V S R axis A z yj)
      (clusterPoint centers M V S R axis B w yi)^2=(ν+α+β)^2-2*α*β := by
  have h := clusterPoint_cross_square centers M V S R axis b₀ b₁ b₂ hfactor A B hAB z w yj yi
  rw [dotProduct_sub] at h
  nlinarith

/-- The absolute cross-error envelope follows from the square identity and a
positive nominal lower bound. No adjacent or differential error bound is used. -/
theorem cross_error_uniform_bound (D u α β B Tmin : ℝ) (hD : 0 ≤ D)
    (hT : 0 < Tmin) (hu : Tmin ≤ u) (hB : |α*β| ≤ B)
    (hsquare : D^2=u^2-2*α*β) : |D-u| ≤ 2*B/Tmin := by
  have hden : 0 < D+u := by linarith
  have heq : D-u=(-2*(α*β))/(D+u) := by
    apply (eq_div_iff hden.ne').2
    nlinarith
  rw [heq,abs_div,abs_mul,abs_of_pos hden]
  norm_num
  have hbound := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ 2 by norm_num)
  have h₀ := div_le_div_of_nonneg_right hbound hden.le
  have h₁ := div_le_div_of_nonneg_left (show 0 ≤ 2*B by nlinarith [abs_nonneg (α*β)]) hT
    (show Tmin ≤ D+u by linarith)
  simpa only [abs_mul] using h₀.trans h₁

end Erdos488.Geometry.SeparatedDistances.FixedDimension
