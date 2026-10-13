module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanClusterCoordinates
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.LocalRulerSeparation

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped Matrix
open Matrix

/-- The actual trigonometric-ruler point; restricting i to Fin k gives the finite configuration. -/
noncomputable def rulerPoint {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (S R axis θ center : ℝ) (p k : ℕ) (A : Fin m) (i : ℕ) :
    EuclideanSpace ℝ (ClusterCoordinate ι m) :=
  clusterPoint centers M V S R axis A (θ*((i : ℝ)-center))
    (3*(primeRuler p k A.val i : ℝ))

/-- The literal Euclidean distance equals the local model, selecting the nonnegative root. -/
theorem rulerPoint_local_distance {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (S R axis θ center b₀ b₁ b₂ : ℝ) (p k : ℕ) (A : Fin m) (i δ : ℕ)
    (hR : R ≠ 0)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2)) :
    dist (rulerPoint centers M V S R axis θ center p k A (i+δ))
      (rulerPoint centers M V S R axis θ center p k A i)=
      localDistanceModel R θ b₁ b₂ δ (rulerArc p k A.val i δ) := by
  have h := clusterPoint_same_cluster_square centers M V S R axis b₀ b₁ b₂ hR hfactor A
    (θ*((i+δ : ℕ)-center)) (θ*((i : ℝ)-center))
    (3*(primeRuler p k A.val (i+δ) : ℝ)) (3*(primeRuler p k A.val i : ℝ))
  have hz : θ*((i+δ : ℕ)-center)-θ*((i : ℝ)-center)=θ*(δ : ℝ) := by push_cast; ring
  have hy : 3*(primeRuler p k A.val (i+δ) : ℝ)-3*(primeRuler p k A.val i : ℝ)=
      rulerArc p k A.val i δ := by
    simp only [rulerArc,primeRulerGap,Int.cast_sub]
    ring
  rw [hz,hy] at h
  have hm := localDistanceModel_square R θ b₁ b₂ δ (rulerArc p k A.val i δ)
  unfold harmonicEnergy at hm
  apply (sq_eq_sq₀ (dist_nonneg) (localDistanceModel_nonneg _ _ _ _ _ _)).1
  change dist (clusterPoint centers M V S R axis A _ _)
    (clusterPoint centers M V S R axis A _ _) ^ 2 = _
  linarith

/-- Actual Euclidean local distances, across all clusters and lags, are separated. -/
theorem rulerPoint_local_pairs_separated {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (S R axis θ center b₀ b₁ b₂ Y J : ℝ) (p k : ℕ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (hp : p.Prime) (hsize : 2*m*k < p)
    (hR : 0 < R) (hY : 12*(p : ℝ)*k ≤ Y) (hangle : Y/(2*R) ≤ Real.pi)
    (hγ : 0 < Real.cos (Y/(2*R))) (hθ : 0 ≤ θ) (hfeature : θ*k ≤ Real.pi/2)
    (hJ : 0 ≤ J) (hJbound : θ^2*(b₁^2+4*b₂^2) ≤ J^2)
    (hguard : 1 ≤ 3*(Real.cos (Y/(2*R))/
      Real.sqrt (1+(J/(9*(p : ℝ)*Real.cos (Y/(2*R))))^2)))
    (A B : Fin m) (i j δ ε : ℕ) (hδ : 0 < δ) (hε : 0 < ε)
    (hδp : δ < p) (hεp : ε < p) (hi : i+δ < k) (hj : j+ε < k)
    (hne : ¬ (A.val=B.val ∧ i=j ∧ δ=ε)) :
    1 ≤ |dist (rulerPoint centers M V S R axis θ center p k A (i+δ))
        (rulerPoint centers M V S R axis θ center p k A i)-
      dist (rulerPoint centers M V S R axis θ center p k B (j+ε))
        (rulerPoint centers M V S R axis θ center p k B j)| := by
  rw [rulerPoint_local_distance centers M V S R axis θ center b₀ b₁ b₂ p k A i δ hR.ne' hfactor,
    rulerPoint_local_distance centers M V S R axis θ center b₀ b₁ b₂ p k B j ε hR.ne' hfactor]
  exact local_ruler_model_separated p m k A.val B.val i j δ ε hp hδ hε hδp hεp hsize
    A.isLt B.isLt hi hj hne R Y θ b₁ b₂ J hR hY hangle hγ hθ hfeature hJ hJbound hguard

/-- Actual Euclidean local pairs are separately bounded away from zero. -/
theorem rulerPoint_local_distance_ge_one {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (S R axis θ center b₀ b₁ b₂ Y : ℝ) (p k : ℕ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (hp : 0 < p) (hR : 0 < R) (hY : 12*(p : ℝ)*k ≤ Y)
    (hangle : Y/(2*R) ≤ Real.pi) (hγ : 0 ≤ Real.cos (Y/(2*R)))
    (hguard : 1 ≤ Real.cos (Y/(2*R))*(9*(p : ℝ)))
    (A : Fin m) (i δ : ℕ) (hδ : 0 < δ) (hi : i+δ < k) :
    1 ≤ dist (rulerPoint centers M V S R axis θ center p k A (i+δ))
      (rulerPoint centers M V S R axis θ center p k A i) := by
  rw [rulerPoint_local_distance centers M V S R axis θ center b₀ b₁ b₂ p k A i δ hR.ne' hfactor]
  exact local_ruler_model_ge_one p k A.val i δ hp hδ hi R Y θ b₁ b₂ hR hY hangle hγ hguard

/-- The additional exact scalar checkpoint from JRL PR3009. The universal source
parameter reduction is separate; this declaration checks its final rational. -/
theorem secant_local_rational_certificate :
    (1 : ℝ) < 35086875845756751025281236528215621632/
      10885060472040642880820354766845703125 := by norm_num

end Erdos488.Geometry.SeparatedDistances.FixedDimension
