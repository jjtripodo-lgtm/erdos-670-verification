module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Subtract the common squared radius from off-diagonal entries only. -/
def offDiagonalShift {ι : Type*} [DecidableEq ι]
    (D : Matrix ι ι ℝ) (r : ℝ) : Matrix ι ι ℝ :=
  fun i j => if i=j then 0 else D i j - 2*r

lemma offDiagonalShift_entry {ι : Type*} [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hdiag : ∀ i, D i i = 0) (r : ℝ) (i j : ι) :
    offDiagonalShift D r i j = D i j - 2*r + if i=j then 2*r else 0 := by
  by_cases h : i=j
  · subst j; simp [offDiagonalShift, hdiag]
  · simp [offDiagonalShift, h]

/-- The exact radius-subtraction identity on every zero-sum vector. Subtracting
from the diagonal too would remove the final term and invalidate this theorem. -/
theorem offDiagonalShift_zero_sum_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hdiag : ∀ i, D i i = 0) (r : ℝ)
    (z : ι → ℝ) (hz : ∑ i, z i = 0) :
    (∑ i, ∑ j, z i * offDiagonalShift D r i j * z j) =
      (∑ i, ∑ j, z i * D i j * z j) + 2*r * ∑ i, z i ^ 2 := by
  simp_rw [offDiagonalShift_entry D hdiag r, mul_add, mul_sub, add_mul, sub_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hconstant : (∑ i, ∑ j, z i * (2*r) * z j) = 0 := by
    simp [← Finset.mul_sum, hz]
  have hdelta : (∑ i, ∑ j, z i * (if i=j then 2*r else 0) * z j) =
      2*r * ∑ i, z i ^ 2 := by
    simp only [mul_ite, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hconstant, sub_zero, hdelta]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
