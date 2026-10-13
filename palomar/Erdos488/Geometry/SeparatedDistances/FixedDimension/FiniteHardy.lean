module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.HardyWeights

@[expose] public section

open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma sum_range_prefix_indicator (g : ℕ → ℝ) {i n : ℕ} (hi : i ≤ n) :
    (∑ j ∈ Finset.range n, if j < i then g j else 0) = ∑ j ∈ Finset.range i, g j := by
  rw [← Finset.sum_range_add_sum_Ico (fun j => if j < i then g j else 0) hi]
  have h₁ : (∑ j ∈ Finset.range i, if j < i then g j else 0) = ∑ j ∈ Finset.range i, g j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  have h₂ : (∑ j ∈ Finset.Ico i n, if j < i then g j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [not_lt.mpr (Finset.mem_Ico.mp hj).1]
  rw [h₁,h₂,add_zero]

lemma sum_range_suffix_indicator (g : ℕ → ℝ) {i n : ℕ} (hi : i ≤ n) :
    (∑ j ∈ Finset.range n, if i ≤ j then g j else 0) = ∑ j ∈ Finset.Ico i n, g j := by
  rw [← Finset.sum_range_add_sum_Ico (fun j => if i ≤ j then g j else 0) hi]
  have h₁ : (∑ j ∈ Finset.range i, if i ≤ j then g j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [not_le.mpr (Finset.mem_range.mp hj)]
  have h₂ : (∑ j ∈ Finset.Ico i n, if i ≤ j then g j else 0) = ∑ j ∈ Finset.Ico i n, g j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [(Finset.mem_Ico.mp hj).1]
  rw [h₁,h₂,zero_add]

noncomputable def hardyMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val < i.val then 1/(i.val+1 : ℕ) else 0

noncomputable def hardyWeight {n : ℕ} (i : Fin n) : ℝ := 1/Real.sqrt (i.val+1 : ℕ)

lemma hardyWeight_pos {n : ℕ} (i : Fin n) : 0 < hardyWeight i := by
  unfold hardyWeight
  positivity

lemma hardyMatrix_row {n : ℕ} (i : Fin n) :
    ∑ j, hardyMatrix n i j * hardyWeight j ≤ 2*hardyWeight i := by
  have heq : (∑ j, hardyMatrix n i j * hardyWeight j) =
      (∑ j ∈ Finset.range i.val, 1/Real.sqrt (j+1 : ℕ))/(i.val+1 : ℕ) := by
    simp only [hardyMatrix,hardyWeight,ite_mul,zero_mul]
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < i.val then 1/(i.val+1:ℕ)*(1/Real.sqrt (j+1:ℕ)) else 0)]
    have hr := sum_range_prefix_indicator (fun j => 1/(i.val+1 : ℕ)*(1/Real.sqrt (j+1 : ℕ))) i.isLt.le
    rw [hr]
    rw [← Finset.mul_sum]
    ring
  rw [heq]
  have hp := sqrt_recip_prefix_sum i.val
  have hm : Real.sqrt (i.val : ℝ) ≤ Real.sqrt (i.val+1 : ℕ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_succ i.val
  apply (div_le_iff₀ (show (0:ℝ)<(i.val+1:ℕ) by positivity)).2
  have hs := Real.sq_sqrt (show (0:ℝ)≤(i.val+1:ℕ) by positivity)
  have hz : Real.sqrt (i.val+1:ℕ) ≠ 0 := ne_of_gt (by positivity)
  have hx : 2*hardyWeight i*(i.val+1:ℕ) = 2*Real.sqrt (i.val+1:ℕ) := by
    unfold hardyWeight
    field_simp [hz]
    nlinarith [hs]
  rw [hx]
  linarith

lemma hardyMatrix_column {n : ℕ} (j : Fin n) :
    ∑ i, hardyMatrix n i j * hardyWeight i ≤ 2*hardyWeight j := by
  have heq : (∑ i, hardyMatrix n i j * hardyWeight i) =
      ∑ i ∈ Finset.Ico (j.val+1) n, 1/((i+1:ℕ)*Real.sqrt (i+1:ℕ)) := by
    simp only [hardyMatrix,hardyWeight,ite_mul,zero_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => if j.val < i then 1/(i+1:ℕ)*(1/Real.sqrt (i+1:ℕ)) else 0)]
    have hterm : ∀ i : ℕ, (if j.val < i then 1/(i+1:ℕ)*(1/Real.sqrt (i+1:ℕ)) else 0) =
      (if j.val+1 ≤ i then 1/((i+1:ℕ)*Real.sqrt (i+1:ℕ)) else 0) := by
      intro i
      simp only [Nat.lt_iff_add_one_le,one_div_mul_one_div]
    simp_rw [hterm]
    exact sum_range_suffix_indicator _ j.isLt
  rw [heq, Finset.sum_Ico_eq_sum_range]
  have ht := sqrt_recip_tail_sum (j.val+1) (n-(j.val+1)) (by omega)
  have ht' : (∑ a ∈ Finset.range (n-(j.val+1)),
      1/((j.val+1+a+1:ℕ)*Real.sqrt (j.val+1+a+1:ℕ))) ≤ 2/Real.sqrt (j.val+1:ℕ) := by
    have hnon : 0 ≤ 1/Real.sqrt (j.val+1+(n-(j.val+1)):ℕ) := by positivity
    rw [div_eq_mul_one_div]
    linarith
  simpa [hardyWeight,div_eq_mul_inv] using ht'

/-- Finite strict-prefix Hardy inequality, constant two in operator norm.
There are no analytic operator estimates among the hypotheses. -/
theorem finite_hardy_two (n : ℕ) (x : Fin n → ℝ) :
    (∑ i, (hardyMatrix n *ᵥ x) i ^ 2) ≤ 4 * ∑ i, x i ^ 2 := by
  apply weighted_schur_two (hardyMatrix n) hardyWeight
  · intro i j
    unfold hardyMatrix
    split_ifs <;> positivity
  · exact hardyWeight_pos
  · exact hardyMatrix_row
  · exact hardyMatrix_column

end Erdos488.Geometry.SeparatedDistances.FixedDimension
