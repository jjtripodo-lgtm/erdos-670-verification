module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section

/-! A source-pinned kernel for the three-active-group Gram completion used in
JRL PR 2974. This module does not assert the construction's analytic bounds or
its final fixed-dimensional configuration theorem. -/

open scoped BigOperators Matrix
open Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma square_sum_three_le (a b c : ℝ) :
    (a + b + c)^2 ≤ 3 * a^2 + 3 * b^2 + 3 * c^2 := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

/-- A whole-matrix completion from three quadratic group budgets. In particular,
the hypotheses must bound each entire group, not each column independently. -/
theorem three_group_completion
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B C : Matrix ι κ ℝ) (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian)
    (hbudget : ∀ x : κ → ℝ,
      3 * ∑ i, (A *ᵥ x) i ^ 2 +
      3 * ∑ i, (B *ᵥ x) i ^ 2 +
      3 * ∑ i, (C *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D *ᵥ x)) :
    (D - (A + B + C)ᵀ * (A + B + C)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact hD.sub (by simpa using Matrix.isHermitian_conjTranspose_mul_self (A+B+C))
  intro x
  have hsum : (∑ i, ((A+B+C) *ᵥ x) i ^ 2) ≤
      3 * ∑ i, (A *ᵥ x) i ^ 2 +
      3 * ∑ i, (B *ᵥ x) i ^ 2 +
      3 * ∑ i, (C *ᵥ x) i ^ 2 := by
    simp only [Matrix.add_mulVec, Pi.add_apply]
    calc
      _ ≤ ∑ i, (3 * (A *ᵥ x) i ^ 2 + 3 * (B *ᵥ x) i ^ 2 +
          3 * (C *ᵥ x) i ^ 2) := Finset.sum_le_sum fun i _ => square_sum_three_le _ _ _
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hgram : x ⬝ᵥ (((A+B+C)ᵀ * (A+B+C)) *ᵥ x) =
      ∑ i, ((A+B+C) *ᵥ x) i ^ 2 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [Matrix.vecMul_transpose]
    simp only [dotProduct, pow_two]
  simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hgram, sub_nonneg] using
    hsum.trans (hbudget x)

/-- The block-diagonal budget may be verified separately for the three groups. -/
theorem three_group_completion_of_separate_budgets
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B C : Matrix ι κ ℝ) (D₀ D₁ D₂ : Matrix κ κ ℝ)
    (h₀ : D₀.IsHermitian) (h₁ : D₁.IsHermitian) (h₂ : D₂.IsHermitian)
    (b₀ : ∀ x : κ → ℝ, 3 * ∑ i, (A *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D₀ *ᵥ x))
    (b₁ : ∀ x : κ → ℝ, 3 * ∑ i, (B *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D₁ *ᵥ x))
    (b₂ : ∀ x : κ → ℝ, 3 * ∑ i, (C *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D₂ *ᵥ x)) :
    (D₀ + D₁ + D₂ - (A+B+C)ᵀ * (A+B+C)).PosSemidef := by
  apply three_group_completion A B C (D₀+D₁+D₂) ((h₀.add h₁).add h₂)
  intro x
  simpa only [Matrix.add_mulVec, dotProduct_add] using add_le_add (add_le_add (b₀ x) (b₁ x)) (b₂ x)

end Erdos488.Geometry.SeparatedDistances.FixedDimension
