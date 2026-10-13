module

public import Erdos488.Geometry.SeparatedDistances.Defs
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletedTrigonometricFeatures

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

abbrev ClusterCoordinate (ι : Type*) (m : ℕ) :=
  ι ⊕ ((Fin m × Fin 2) ⊕ (Fin m ⊕ (Fin m × Fin 5)))

noncomputable def privateCircle {m : ℕ} (A : Fin m) (R y : ℝ) : Fin m × Fin 2 → ℝ :=
  fun q => if q.1=A then ![R*Real.cos (y/R),R*Real.sin (y/R)] q.2 else 0

/-- Literal finite Euclidean coordinates; macro, private plane, axis, residual. -/
noncomputable def clusterPoint {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis : ℝ)
    (A : Fin m) (z y : ℝ) : EuclideanSpace ℝ (ClusterCoordinate ι m) :=
  WithLp.toLp 2 (Sum.elim (fun q => S*centers A q+(M *ᵥ clusteredFeature A z) q)
    (Sum.elim (privateCircle A R y)
      (Sum.elim (fun B => if B=A then axis else 0) (V *ᵥ clusteredFeature A z))))

theorem privateCircle_difference_square {m : ℕ} (A : Fin m) (R yj yi : ℝ) :
    (∑ q, (privateCircle A R yj q-privateCircle A R yi q)^2)=
      (R*Real.cos (yj/R)-R*Real.cos (yi/R))^2+
      (R*Real.sin (yj/R)-R*Real.sin (yi/R))^2 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ B : Fin m, (∑ a : Fin 2,
      (privateCircle A R yj (B,a)-privateCircle A R yi (B,a))^2)=
      if B=A then (R*Real.cos (yj/R)-R*Real.cos (yi/R))^2+
        (R*Real.sin (yj/R)-R*Real.sin (yi/R))^2 else 0 := by
    intro B
    by_cases h : B=A <;> simp [privateCircle,h,Fin.sum_univ_succ]
  simp_rw [he]
  simp

/-- Actual Euclidean same-cluster distance, including all coordinate blocks. -/
theorem clusterPoint_same_cluster_square {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis b₀ b₁ b₂ : ℝ)
    (hR : R ≠ 0)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A : Fin m) (z w yj yi : ℝ) :
    dist (clusterPoint centers M V S R axis A z yj)
      (clusterPoint centers M V S R axis A w yi)^2=
      (circleChord R (yj-yi))^2+(2*b₁*Real.sin ((z-w)/2))^2+
        (2*b₂*Real.sin (z-w))^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [clusterPoint,WithLp.ofLp_toLp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Real.dist_eq,sq_abs,add_sub_add_left_eq_sub,sub_self,zero_pow,Finset.sum_const_zero,zero_add]
  rw [privateCircle_difference_square]
  simp only [show (0 : ℝ)^2=0 by norm_num,Finset.sum_const_zero,zero_add]
  have hc := circle_chord_coordinate_square R yj yi hR
  have hf := completed_feature_difference_square M V b₀ b₁ b₂ hfactor A z w
  linarith

/-- The intended coordinate count is exactly 9m-1 when the macro space has m-1 coordinates. -/
theorem clusterCoordinate_card (m : ℕ) (hm : 0 < m) :
    Fintype.card (ClusterCoordinate (Fin (m-1)) m)=9*m-1 := by
  simp only [ClusterCoordinate,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

end Erdos488.Geometry.SeparatedDistances.FixedDimension
