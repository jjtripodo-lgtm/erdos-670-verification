module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.PotentialSolve
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma nonnegative_weighted_cauchy {ι : Type*} [Fintype ι]
    (a w x : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 < w i) :
    (∑ i, a i*x i)^2 ≤ (∑ i, a i*w i) * ∑ i, a i/w i*x i^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (a i)*Real.sqrt (w i))
    (fun i => Real.sqrt (a i)/Real.sqrt (w i)*x i)
  have hs : ∀ i, Real.sqrt (w i) ≠ 0 := fun i => ne_of_gt (Real.sqrt_pos.2 (hw i))
  have hprod : ∀ i, (Real.sqrt (a i)*Real.sqrt (w i)) *
      (Real.sqrt (a i)/Real.sqrt (w i)*x i) = a i*x i := by
    intro i
    have hh := Real.sq_sqrt (ha i)
    field_simp [hs i]
    rw [hh]
    ring
  have hf : ∀ i, (Real.sqrt (a i)*Real.sqrt (w i))^2 = a i*w i := by
    intro i
    rw [mul_pow, Real.sq_sqrt (ha i), Real.sq_sqrt (hw i).le]
  have hg : ∀ i, (Real.sqrt (a i)/Real.sqrt (w i)*x i)^2 = a i/w i*x i^2 := by
    intro i
    rw [mul_pow, div_pow, Real.sq_sqrt (ha i), Real.sq_sqrt (hw i).le]
  simpa only [hprod,hf,hg] using h

/-- Finite weighted Schur test at the Hardy constant two, stated as a
simultaneous quadratic-form bound for every input vector. -/
theorem weighted_schur_two {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (w : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, A i j*w j ≤ 2*w i)
    (hcol : ∀ j, ∑ i, A i j*w i ≤ 2*w j)
    (x : ι → ℝ) :
    (∑ i, (A *ᵥ x) i ^ 2) ≤ 4*∑ j, x j ^ 2 := by
  have hlocal : ∀ i, (A *ᵥ x) i ^ 2 ≤ 2*w i * ∑ j, A i j/w j*x j^2 := by
    intro i
    have hc := nonnegative_weighted_cauchy (A i) w x (hA i) hw
    have hz : 0 ≤ ∑ j, A i j/w j*x j^2 := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (div_nonneg (hA i j) (hw j).le) (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right (hrow i) hz
    simpa only [Matrix.mulVec, dotProduct] using hc.trans hh
  calc
    _ ≤ ∑ i, 2*w i * ∑ j, A i j/w j*x j^2 :=
      Finset.sum_le_sum fun i _ => hlocal i
    _ = ∑ j, (2*(∑ i, A i j*w i)/w j)*x j^2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ j, 4*x j^2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply (div_le_iff₀ (hw j)).2
      linarith [hcol j]
    _ = _ := by rw [Finset.mul_sum]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
