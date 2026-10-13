module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.GlobalCompletion
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-! A fixed-coordinate-count PSD residual factor, for the global completion.
Unlike an existential finite-dimensional Gram realization, this does not hide
an unbounded auxiliary dimension. -/

open scoped BigOperators Matrix MatrixOrder
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Every real PSD matrix has a Gram factor with exactly the same index type. -/
theorem psd_same_size_gram_factor {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Q : Matrix κ κ ℝ) (hQ : Q.PosSemidef) :
    ∃ V : Matrix κ κ ℝ, Vᵀ * V = Q := by
  refine ⟨CFC.sqrt Q, ?_⟩
  have hs := (CFC.sqrt_nonneg Q).isSelfAdjoint
  have hstar : (CFC.sqrt Q)ᵀ = CFC.sqrt Q := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hs.star_eq
  rw [hstar, ← pow_two]
  exact CFC.sq_sqrt Q hQ.nonneg

/-- The residual occupies κ coordinates; the original output occupies ι.
The factor has no additional dimension depending on the number of points. -/
theorem three_group_completion_factor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B C : Matrix ι κ ℝ) (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian)
    (hbudget : ∀ x : κ → ℝ,
      3 * ∑ i, (A *ᵥ x) i ^ 2 +
      3 * ∑ i, (B *ᵥ x) i ^ 2 +
      3 * ∑ i, (C *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D *ᵥ x)) :
    ∃ V : Matrix κ κ ℝ, (A+B+C)ᵀ*(A+B+C) + Vᵀ*V = D := by
  obtain ⟨V, hV⟩ := psd_same_size_gram_factor _
    (three_group_completion A B C D hD hbudget)
  refine ⟨V, ?_⟩
  rw [hV]
  abel

/-- Exact cancellation of the combined macro and residual inner products. -/
theorem completed_bilinear_identity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (V D : Matrix κ κ ℝ)
    (hfactor : Mᵀ*M + Vᵀ*V = D) (x y : κ → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ y) + (V *ᵥ x) ⬝ᵥ (V *ᵥ y) =
      x ⬝ᵥ (D *ᵥ y) := by
  rw [← hfactor, Matrix.add_mulVec, dotProduct_add]
  congr 1 <;> rw [← Matrix.mulVec_mulVec] <;> symm <;>
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
