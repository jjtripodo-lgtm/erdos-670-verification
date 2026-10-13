module

public import Erdos488.Geometry.SeparatedDistances.PrefixSums
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators
open Matrix

/-- A positive-definite real matrix is the Gram matrix of independent standard Euclidean vectors. -/
theorem posDef_exists_euclidean_independent_gram {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      Matrix.gram ℝ v = B ∧ LinearIndependent ℝ v := by
  obtain ⟨E, instNorm, instInner, instFD, u, hGram, hLI, hdim⟩ :=
    posDef_exists_fd_independent_gram B hB
  letI := instNorm
  letI := instInner
  letI := instFD
  let b := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  let L := b.repr
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => L (u i)
  have hvGram : Matrix.gram ℝ v = B := by
    ext i j
    change inner ℝ (L (u i)) (L (u j)) = B i j
    exact (L.inner_map_map (u i) (u j)).trans (congrFun (congrFun hGram i) j)
  have hvLI : LinearIndependent ℝ v := by
    exact hLI.map_injOn L.toLinearMap L.injective.injOn
  exact ⟨v, hvGram, hvLI⟩

/-- Extend a finite family by zero to natural-number indices. -/
def finExtendZero {n : ℕ} {E : Type*} [Zero E] (v : Fin n → E) (a : ℕ) : E :=
  if h : a < n then v ⟨a, h⟩ else 0

/-- A finite prefix sum equals the corresponding range sum of the zero extension. -/
theorem prefixSums_eq_sum_range {n : ℕ} {E : Type*} [AddCommMonoid E]
    (v : Fin n → E) (j : Fin n) :
    prefixSums v j = ∑ a ∈ Finset.range (j.val + 1), finExtendZero v a := by
  let e : Fin (j.val + 1) ≃ {i : Fin n // i.val < j.val + 1} :=
    Fin.castLEquiv (Nat.succ_le_iff.mpr j.isLt)
  have hsub :
      (∑ i : {i : Fin n // i.val < j.val + 1}, v i) =
        ∑ i : Fin (j.val + 1), v (e i) := by
    exact (Fintype.sum_equiv e (fun i => v (e i)) (fun i => v i) (fun _ => rfl)).symm
  rw [prefixSums]
  calc
    (∑ i : Fin n with i ≤ j, v i) =
        ∑ i : {i : Fin n // i.val < j.val + 1}, v i := by
          apply Finset.sum_subtype
          intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
    _ = ∑ i : Fin (j.val + 1), v (e i) := hsub
    _ = ∑ a ∈ Finset.range (j.val + 1), finExtendZero v a := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' : a < j.val + 1 := Finset.mem_range.mp ha
      have han : a < n := lt_of_lt_of_le ha' (Nat.succ_le_iff.mpr j.isLt)
      have haj : a ≤ j.val := by omega
      simp [e, finExtendZero, han, haj]

/-- Cumulative points are natural-number partial sums of the zero-extended increments. -/
theorem cumulativePoints_eq_sum_range {n : ℕ} {E : Type*} [AddCommMonoid E]
    (v : Fin n → E) (j : Fin (n + 1)) :
    cumulativePoints v j = ∑ a ∈ Finset.range j.val, finExtendZero v a := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [cumulativePoints]
  · simpa [cumulativePoints] using prefixSums_eq_sum_range v k

/-- Extend finite squared-distance data by zero outside its vertex range. -/
def sqDistanceExtendZero {n : ℕ} (D : SqDistanceData (Fin (n + 1)))
    (a b : ℕ) : ℝ :=
  if ha : a < n + 1 then
    if hb : b < n + 1 then D ⟨a, ha⟩ ⟨b, hb⟩ else 0
  else 0

theorem sqDistanceExtendZero_symmetric {n : ℕ} (D : SqDistanceData (Fin (n + 1)))
    (hD : D.IsHermitian) (a b : ℕ) :
    sqDistanceExtendZero D a b = sqDistanceExtendZero D b a := by
  by_cases ha : a < n + 1 <;> by_cases hb : b < n + 1
  · simp only [sqDistanceExtendZero, ha, hb, ↓reduceDIte]
    simpa only [star_trivial] using hD.apply ⟨b, hb⟩ ⟨a, ha⟩
  · simp [sqDistanceExtendZero, ha, hb]
  · simp [sqDistanceExtendZero, ha, hb]
  · simp [sqDistanceExtendZero, ha, hb]

theorem sqDistanceExtendZero_diag {n : ℕ} (D : SqDistanceData (Fin (n + 1)))
    (hdiag : ∀ i, D i i = 0) (a : ℕ) : sqDistanceExtendZero D a a = 0 := by
  by_cases ha : a < n + 1
  · simp [sqDistanceExtendZero, ha, hdiag]
  · simp [sqDistanceExtendZero, ha]

/-- Positive increment Gram data realize all ordered squared distances in standard Euclidean space. -/
theorem posDef_incrementGram_realizes_in_euclideanSpace_ordered {n : ℕ}
    (D : SqDistanceData (Fin (n + 1))) (hDsym : D.IsHermitian)
    (hdiag : ∀ i, D i i = 0) (hB : (incrementGram D).PosDef) :
    ∃ p : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
      AffineIndependent ℝ p ∧
      ∀ i j : Fin (n + 1), i.val ≤ j.val → ‖p j - p i‖ ^ 2 = D i j := by
  obtain ⟨v, hvGram, hvLI⟩ :=
    posDef_exists_euclidean_independent_gram (incrementGram D) hB
  let p := cumulativePoints v
  refine ⟨p, affineIndependent_cumulativePoints v hvLI, ?_⟩
  intro i j hij
  rw [show p j = ∑ a ∈ Finset.range j.val, finExtendZero v a from
        cumulativePoints_eq_sum_range v j,
      show p i = ∑ a ∈ Finset.range i.val, finExtendZero v a from
        cumulativePoints_eq_sum_range v i,
      partial_sum_sub_partial_sum (finExtendZero v) hij,
      norm_sq_block_sum_eq_gram_sum]
  have hsum :
      (∑ a ∈ Finset.Ico i.val j.val, ∑ b ∈ Finset.Ico i.val j.val,
        Matrix.gram ℝ (finExtendZero v) a b) =
      ∑ a ∈ Finset.Ico i.val j.val, ∑ b ∈ Finset.Ico i.val j.val,
        (-(1 / 2 : ℝ) *
          (sqDistanceExtendZero D (a + 1) (b + 1) -
           sqDistanceExtendZero D (a + 1) b -
           sqDistanceExtendZero D a (b + 1) +
           sqDistanceExtendZero D a b)) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hai : i.val ≤ a := (Finset.mem_Ico.mp ha).1
    have haj : a < j.val := (Finset.mem_Ico.mp ha).2
    have han : a < n := lt_of_lt_of_le haj (Nat.lt_succ_iff.mp j.isLt)
    apply Finset.sum_congr rfl
    intro b hb
    have hbj : b < j.val := (Finset.mem_Ico.mp hb).2
    have hbn : b < n := lt_of_lt_of_le hbj (Nat.lt_succ_iff.mp j.isLt)
    have hgramab := congrFun (congrFun hvGram ⟨a, han⟩) ⟨b, hbn⟩
    simp only [Matrix.gram_apply, finExtendZero, han, hbn, ↓reduceDIte] at hgramab ⊢
    rw [hgramab]
    simp [incrementGram, sqDistanceExtendZero, han, hbn, Nat.lt_succ_of_lt han,
      Nat.lt_succ_of_lt hbn]
  rw [hsum]
  rw [mixed_difference_block_eq_distance (sqDistanceExtendZero D)
    (sqDistanceExtendZero_symmetric D hDsym)
    (sqDistanceExtendZero_diag D hdiag) hij]
  simp [sqDistanceExtendZero, i.isLt, j.isLt]

/-- Positive increment Gram data realize all squared distances in standard Euclidean space. -/
theorem posDef_incrementGram_realizes_in_euclideanSpace {n : ℕ}
    (D : SqDistanceData (Fin (n + 1))) (hDsym : D.IsHermitian)
    (hdiag : ∀ i, D i i = 0) (hB : (incrementGram D).PosDef) :
    ∃ p : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
      AffineIndependent ℝ p ∧ ∀ i j, ‖p j - p i‖ ^ 2 = D i j := by
  obtain ⟨p, hpaff, hp⟩ :=
    posDef_incrementGram_realizes_in_euclideanSpace_ordered D hDsym hdiag hB
  refine ⟨p, hpaff, ?_⟩
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact hp i j hij
  · have hji : j.val ≤ i.val := Nat.le_of_lt (Nat.lt_of_not_ge hij)
    have h := hp j i hji
    have hnorm : ‖p j - p i‖ = ‖p i - p j‖ := by
      rw [show p j - p i = -(p i - p j) by abel, norm_neg]
    have hD : D j i = D i j := by
      simpa only [star_trivial] using hDsym.apply i j
    rw [hnorm, h, hD]

end Erdos488.Geometry.SeparatedDistances
