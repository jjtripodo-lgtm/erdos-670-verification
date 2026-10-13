module

public import Erdos488.Geometry.SeparatedDistances.GramRealization
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators
open Matrix

/-- The nonzero prefix sums of a finite family. -/
def prefixSums {n : ℕ} {E : Type*} [AddCommMonoid E]
    (u : Fin n → E) (j : Fin n) : E :=
  ∑ i : Fin n with i ≤ j, u i

/-- The coefficient matrix whose columns are the prefix vectors. -/
def prefixMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ≤ j then 1 else 0

theorem prefixMatrix_det (n : ℕ) : (prefixMatrix n).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [prefixMatrix]
  · intro i j hji
    have hji' : j < i := by simpa using hji
    simp [prefixMatrix, not_le.mpr hji']

theorem prefixMatrix_columns_linearIndependent (n : ℕ) :
    LinearIndependent ℝ (prefixMatrix n)ᵀ := by
  apply Matrix.linearIndependent_cols_of_det_ne_zero
  rw [prefixMatrix_det]
  norm_num

/-- Prefix sums of a linearly independent finite family remain linearly independent. -/
theorem linearIndependent_prefixSums {n : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (u : Fin n → E)
    (hu : LinearIndependent ℝ u) : LinearIndependent ℝ (prefixSums u) := by
  let L : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ u
  have hLinj : Function.Injective L := by
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp hu
  have hmapped : LinearIndependent ℝ (L ∘ (prefixMatrix n)ᵀ) :=
    (prefixMatrix_columns_linearIndependent n).map_injOn L hLinj.injOn
  have heq : L ∘ (prefixMatrix n)ᵀ = prefixSums u := by
    funext j
    change Fintype.linearCombination ℝ u ((prefixMatrix n)ᵀ j) = prefixSums u j
    rw [Fintype.linearCombination_apply]
    simp only [transpose_apply, prefixMatrix, prefixSums]
    simpa only [ite_smul, one_smul, zero_smul] using
      (Finset.sum_filter (s := Finset.univ) (fun i : Fin n => i ≤ j) u).symm
  rwa [heq] at hmapped

/-- The origin followed by the nonzero prefix sums. -/
def cumulativePoints {n : ℕ} {E : Type*} [AddCommMonoid E]
    (u : Fin n → E) : Fin (n + 1) → E :=
  Fin.cons 0 (prefixSums u)

/-- Successor indices are exactly the nonzero indices of `Fin (n+1)`. -/
def finSuccNeZeroEquiv (n : ℕ) : Fin n ≃ {j : Fin (n + 1) // j ≠ 0} where
  toFun i := ⟨i.succ, Fin.succ_ne_zero i⟩
  invFun j := ⟨j.1.val - 1, by
    have hjpos : 0 < j.1.val := by
      apply Nat.pos_of_ne_zero
      intro hj
      apply j.2
      apply Fin.ext
      simpa using hj
    omega⟩
  left_inv i := by ext; simp
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.succ_mk]
    have hjpos : 0 < j.1.val := by
      apply Nat.pos_of_ne_zero
      intro hj
      apply j.2
      apply Fin.ext
      simpa using hj
    omega

/-- Cumulative points of independent increments are affinely independent. -/
theorem affineIndependent_cumulativePoints {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (u : Fin n → E)
    (hu : LinearIndependent ℝ u) : AffineIndependent ℝ (cumulativePoints u) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ (cumulativePoints u) 0]
  rw [← linearIndependent_equiv (finSuccNeZeroEquiv n)]
  simpa [Function.comp_def, cumulativePoints, finSuccNeZeroEquiv] using
    linearIndependent_prefixSums u hu

end Erdos488.Geometry.SeparatedDistances
