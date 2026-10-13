module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.HarmonicLocalModel

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators

/-- The literal five coordinates used by the completed construction. -/
noncomputable def trigFeature (z : ℝ) : Fin 5 → ℝ :=
  ![1,Real.sin z,Real.cos z,Real.sin (2*z),Real.cos (2*z)]

/-- One exact diagonal reserve block. -/
def trigWeight (b₀ b₁ b₂ : ℝ) : Fin 5 → ℝ := ![b₀^2,b₁^2,b₁^2,b₂^2,b₂^2]

/-- The weighted feature norm is independent of the local point. -/
theorem trigFeature_constant_norm (b₀ b₁ b₂ z : ℝ) :
    (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*(trigFeature z a)^2)=b₀^2+b₁^2+b₂^2 := by
  simp only [Fin.sum_univ_succ,trigFeature,trigWeight,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero,one_pow,mul_one]
  have h₁ := congrArg (fun x : ℝ => b₁^2*x) (Real.sin_sq_add_cos_sq z)
  have h₂ := congrArg (fun x : ℝ => b₂^2*x) (Real.sin_sq_add_cos_sq (2*z))
  nlinarith only [h₁,h₂]

/-- The full weighted five-coordinate difference gives precisely two harmonics. -/
theorem trigFeature_difference_square (b₀ b₁ b₂ z w : ℝ) :
    (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*(trigFeature z a-trigFeature w a)^2)=
      (2*b₁*Real.sin ((z-w)/2))^2+(2*b₂*Real.sin (z-w))^2 := by
  have h₁ := congrArg (fun x : ℝ => b₁^2*x) (unit_circle_chord_square z w)
  have h₂ := congrArg (fun x : ℝ => b₂^2*x) (unit_circle_chord_square (2*z) (2*w))
  rw [show (2*z-2*w)/2=z-w by ring] at h₂
  simp only [Fin.sum_univ_succ,trigFeature,trigWeight,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero,sub_self]
  nlinarith only [h₁,h₂]

/-- Centering cancels from feature differences, leaving only the local lag. -/
theorem trigFeature_centered_difference (b₀ b₁ b₂ θ center i j : ℝ) :
    (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*
      (trigFeature (θ*(j-center)) a-trigFeature (θ*(i-center)) a)^2)=
      harmonicEnergy θ b₁ b₂ (j-i) := by
  rw [trigFeature_difference_square]
  have h : θ*(j-center)-θ*(i-center)=θ*(j-i) := by ring
  simp only [h,harmonicEnergy]

/-- Adding the private circle gives the literal local-model squared length. -/
theorem circle_and_feature_local_square (R b₀ b₁ b₂ θ center i j yi yj : ℝ)
    (hR : R ≠ 0) :
    (R*Real.cos (yj/R)-R*Real.cos (yi/R))^2+
      (R*Real.sin (yj/R)-R*Real.sin (yi/R))^2+
      (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*
        (trigFeature (θ*(j-center)) a-trigFeature (θ*(i-center)) a)^2)=
    (localDistanceModel R θ b₁ b₂ (j-i) (yj-yi))^2 := by
  rw [circle_chord_coordinate_square R yj yi hR,trigFeature_centered_difference,
    localDistanceModel_square]

/-- Embed a feature into its own five-coordinate macro-cluster block. -/
noncomputable def clusteredFeature {m : ℕ} (A : Fin m) (z : ℝ) : Fin m × Fin 5 → ℝ :=
  fun q => if q.1=A then trigFeature z q.2 else 0

/-- Literal block disjointness, with no orthogonality assumption. -/
theorem clusteredFeature_weighted_dot {m : ℕ} (A B : Fin m) (b₀ b₁ b₂ z w : ℝ) :
    (∑ q : Fin m × Fin 5, trigWeight b₀ b₁ b₂ q.2*
      clusteredFeature A z q*clusteredFeature B w q)=
    if A=B then ∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*trigFeature z a*trigFeature w a else 0 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ C : Fin m,
      (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*clusteredFeature A z (C,a)*
        clusteredFeature B w (C,a)) =
      if C=A then (if A=B then ∑ a : Fin 5,
        trigWeight b₀ b₁ b₂ a*trigFeature z a*trigFeature w a else 0) else 0 := by
    intro C
    by_cases hC : C=A
    · subst C
      by_cases hAB : A=B <;> simp [clusteredFeature,hAB]
    · simp [clusteredFeature,hC]
  simp_rw [he]
  simp

/-- Constant feature reserve survives embedding in the full 5m-coordinate space. -/
theorem clusteredFeature_constant_norm {m : ℕ} (A : Fin m) (b₀ b₁ b₂ z : ℝ) :
    (∑ q : Fin m × Fin 5, trigWeight b₀ b₁ b₂ q.2*(clusteredFeature A z q)^2)=
      b₀^2+b₁^2+b₂^2 := by
  have h := clusteredFeature_weighted_dot A A b₀ b₁ b₂ z z
  simp only [if_pos rfl] at h
  simp_rw [mul_assoc,← sq] at h
  exact h.trans (trigFeature_constant_norm b₀ b₁ b₂ z)

/-- The same-cluster feature difference lives in one block and retains its harmonics. -/
theorem clusteredFeature_difference_square {m : ℕ} (A : Fin m) (b₀ b₁ b₂ z w : ℝ) :
    (∑ q : Fin m × Fin 5, trigWeight b₀ b₁ b₂ q.2*
      (clusteredFeature A z q-clusteredFeature A w q)^2)=
      (2*b₁*Real.sin ((z-w)/2))^2+(2*b₂*Real.sin (z-w))^2 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ C : Fin m,
      (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*
        (clusteredFeature A z (C,a)-clusteredFeature A w (C,a))^2)=
      if C=A then ∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*(trigFeature z a-trigFeature w a)^2 else 0 := by
    intro C
    by_cases hC : C=A <;> simp [clusteredFeature,hC]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact trigFeature_difference_square b₀ b₁ b₂ z w

end Erdos488.Geometry.SeparatedDistances.FixedDimension
