module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.FiniteHardy

@[expose] public section

open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Diagonal-weighted strict upper triangular fine incidence. -/
noncomputable def fineTriangle (n : ℕ) (P : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val < j.val then 1/P i else 0

/-- A uniform denominator bound controls the entire fine matrix. -/
theorem fineTriangle_bound {n : ℕ} (P : Fin n → ℝ) {K : ℝ}
    (hK : 0 < K) (hn : (n:ℝ) ≤ K) (hP : ∀ i, K ≤ P i) (x : Fin n → ℝ) :
    (∑ i, (fineTriangle n P *ᵥ x) i ^ 2) ≤ ∑ i, x i ^ 2 := by
  have ha : ∀ i j, (fineTriangle n P i j)^2 ≤ 1/K^2 := by
    intro i j
    unfold fineTriangle
    split_ifs
    · rw [div_pow,one_pow]
      apply one_div_le_one_div_of_le (sq_pos_of_pos hK)
      nlinarith [hP i]
    · simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      positivity
  have hx : 0 ≤ ∑ j, x j^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hl : ∀ i, (fineTriangle n P *ᵥ x) i ^ 2 ≤ ((n:ℝ)/K^2)*∑ j, x j^2 := by
    intro i
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fineTriangle n P i) x
    have hs : ∑ j, (fineTriangle n P i j)^2 ≤ (n:ℝ)/K^2 := by
      calc
        _ ≤ ∑ j : Fin n, 1/K^2 := Finset.sum_le_sum fun j _ => ha i j
        _ = _ := by simp; ring
    exact hc.trans (mul_le_mul_of_nonneg_right hs hx)
  calc
    _ ≤ ∑ i : Fin n, ((n:ℝ)/K^2)*∑ j, x j^2 := Finset.sum_le_sum fun i _ => hl i
    _ = ((n:ℝ)^2/K^2)*∑ j, x j^2 := by simp; ring
    _ ≤ 1*∑ j, x j^2 := by
      apply mul_le_mul_of_nonneg_right _ hx
      apply (div_le_iff₀ (sq_pos_of_pos hK)).2
      nlinarith [sq_nonneg ((n:ℝ)-K)]
    _ = _ := one_mul _

/-- Literal normalized lower-triangular coarse incidence. -/
noncomputable def coarseTriangle (n : ℕ) (P : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val < i.val then (i.val:ℝ)/P i else 0

/-- The coarse triangular estimate consumes the proved Hardy inequality,
not a per-column or unproved operator premise. -/
theorem coarseTriangle_bound {n : ℕ} (P : Fin n → ℝ)
    (hP : ∀ i, 0 < P i)
    (hquad : ∀ i, (i.val:ℝ)*(i.val+1) ≤ 2*P i) (x : Fin n → ℝ) :
    (∑ i, (coarseTriangle n P *ᵥ x) i ^ 2) ≤ 16*∑ i, x i ^ 2 := by
  let q : Fin n → ℝ := fun i => (i.val:ℝ)*(i.val+1)/P i
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hP i).le
  have hq2 : ∀ i, q i ≤ 2 := by
    intro i
    exact (div_le_iff₀ (hP i)).2 (hquad i)
  have he : ∀ i, (coarseTriangle n P *ᵥ x) i = q i*(hardyMatrix n *ᵥ x) i := by
    intro i
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold coarseTriangle hardyMatrix q
    split_ifs
    · have hz : (i.val:ℝ)+1 ≠ 0 := by positivity
      norm_num only [Nat.cast_add,Nat.cast_one]
      field_simp
    · ring
  calc
    _ = ∑ i, (q i)^2*(hardyMatrix n *ᵥ x) i^2 := by simp_rw [he,mul_pow]
    _ ≤ ∑ i, 4*(hardyMatrix n *ᵥ x) i^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [hq0 i,hq2 i]
    _ = 4*∑ i, (hardyMatrix n *ᵥ x) i^2 := by rw [Finset.mul_sum]
    _ ≤ 4*(4*∑ i, x i^2) := mul_le_mul_of_nonneg_left (finite_hardy_two n x) (by norm_num)
    _ = _ := by ring


/-- The literal colex diagonal satisfies the coarse Hardy domination. -/
lemma colex_triangle_denominator {K : ℝ} (hK : 0 ≤ K) (i : ℕ) :
    (i:ℝ)*(i+1) ≤ 2*colexANat K (i+1) := by
  unfold colexANat
  push_cast [Nat.cast_choose_two]
  nlinarith

lemma colex_triangle_positive {K : ℝ} (hK : 0 < K) (i : ℕ) :
    0 < colexANat K (i+1) := by
  unfold colexANat
  positivity

/-- Both complementary triangular bounds with the actual colex diagonal. -/
theorem colex_fine_coarse_triangle_bounds {n : ℕ} {K : ℝ}
    (hK : 0 < K) (hn : (n:ℝ) ≤ K) (x : Fin n → ℝ) :
    (∑ i, (fineTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i^2) ≤ ∑ i, x i^2 ∧
    (∑ i, (coarseTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i^2) ≤ 16*∑ i, x i^2 := by
  constructor
  · apply fineTriangle_bound _ hK hn
    intro i
    unfold colexANat
    exact le_add_of_nonneg_right (by positivity)
  · apply coarseTriangle_bound
    · exact fun i => colex_triangle_positive hK i.val
    · exact fun i => colex_triangle_denominator hK.le i.val

/-- Adding the diagonal keeps the fine and coarse whole-matrix constants 2 and 5. -/
theorem colex_fine_coarse_full_bounds {n : ℕ} {K : ℝ}
    (hK : 0 < K) (hn : (n:ℝ) ≤ K) (x : Fin n → ℝ) :
    (∑ i, (x i-(fineTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i)^2) ≤ 4*∑ i, x i^2 ∧
    (∑ i, (x i+(coarseTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i)^2) ≤ 25*∑ i, x i^2 := by
  obtain ⟨hf,hc⟩ := colex_fine_coarse_triangle_bounds hK hn x
  constructor
  · calc
      _ ≤ ∑ i, (2*x i^2+2*(fineTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i^2) := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [sq_nonneg (x i+(fineTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i)]
      _ = 2*(∑ i, x i^2)+2*(∑ i, (fineTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i^2) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      _ ≤ _ := by linarith
  · calc
      _ ≤ ∑ i, (5*x i^2+(5/4:ℝ)*(coarseTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i^2) := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [sq_nonneg (4*x i-(coarseTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i)]
      _ = 5*(∑ i, x i^2)+(5/4:ℝ)*(∑ i, (coarseTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i^2) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      _ ≤ _ := by linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
