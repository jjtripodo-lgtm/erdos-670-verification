module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceActualCrossMetric

@[expose] public section

/-! Reindex the actual cross edges by the source's contiguous colex code so
the already proved complete cross-spectrum theorem applies to their distances. -/

open scoped BigOperators Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

public theorem sourcePairCode_exists_pair {m : ℕ}
    (a : Fin (Nat.choose (m+1) 2)) :
    ∃ q : Fin (m+1) × Fin (m+1),
      q.1.val < q.2.val ∧ sourcePairCode q.1 q.2 = a.val := by
  obtain ⟨A, J, hAJ, hcode⟩ := sourcePairCode_surjective a.val a.isLt
  exact ⟨(A,J), hAJ, hcode⟩

noncomputable def sourcePairDecode {m : ℕ}
    (a : Fin (Nat.choose (m+1) 2)) : Fin (m+1) × Fin (m+1) :=
  Classical.choose (sourcePairCode_exists_pair a)

theorem sourcePairDecode_spec {m : ℕ}
    (a : Fin (Nat.choose (m+1) 2)) :
    (sourcePairDecode a).1.val < (sourcePairDecode a).2.val ∧
      sourcePairCode (sourcePairDecode a).1 (sourcePairDecode a).2 = a.val :=
  Classical.choose_spec (sourcePairCode_exists_pair a)

theorem sourcePairDecode_code {m : ℕ}
    (A J : Fin (m+1)) (hAJ : A.val < J.val) :
    sourcePairDecode ⟨sourcePairCode A J,
      sourcePairCode_lt_choose A J hAJ⟩ = (A,J) := by
  let a : Fin (Nat.choose (m+1) 2) :=
    ⟨sourcePairCode A J, sourcePairCode_lt_choose A J hAJ⟩
  have hspec := sourcePairDecode_spec a
  obtain ⟨hA, hJ⟩ := sourcePairCode_ordered_injective
    (sourcePairDecode a).1 (sourcePairDecode a).2 A J
    hspec.1 hAJ (by simpa [a] using hspec.2)
  exact Prod.ext hA hJ

noncomputable def sourceRealizedCrossDistance {m k : ℕ}
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (a i j : ℕ) : ℝ :=
  if ha : a < Nat.choose (m+1) 2 then
    if hi : i < k then
      if hj : j < k then
        dist (P ((sourcePairDecode ⟨a,ha⟩).1, ⟨i,hi⟩))
          (P ((sourcePairDecode ⟨a,ha⟩).2, ⟨j,hj⟩))
      else 0
    else 0
  else 0

theorem sourceRealizedCrossDistance_eq {m k : ℕ}
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (a i j : ℕ) (ha : a < Nat.choose (m+1) 2)
    (hi : i < k) (hj : j < k) :
    sourceRealizedCrossDistance P a i j =
      dist (P ((sourcePairDecode ⟨a,ha⟩).1, ⟨i,hi⟩))
        (P ((sourcePairDecode ⟨a,ha⟩).2, ⟨j,hj⟩)) := by
  simp [sourceRealizedCrossDistance, ha, hi, hj]

theorem sourceRealizedCrossDistance_pair {m k : ℕ}
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (A J : Fin (m+1)) (hAJ : A.val < J.val) (i j : Fin k) :
    sourceRealizedCrossDistance P (sourcePairCode A J) i.val j.val =
      dist (P (A,i)) (P (J,j)) := by
  rw [sourceRealizedCrossDistance_eq P _ _ _
    (sourcePairCode_lt_choose A J hAJ) i.isLt j.isLt]
  rw [sourcePairDecode_code A J hAJ]

theorem sourceRealizedCrossDistance_square {m k : ℕ}
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (hcross : ∀ A J : Fin (m+1), A.val < J.val →
      ∀ i j : Fin k,
        dist (P (A,i)) (P (J,j))^2 =
          (sourceCrossBaseline (sourceOffset (m+1) : ℝ) k
              (sourcePairCode A J) +
            sourceAlpha k i.val + sourceBeta k j.val)^2 -
            2*sourceAlpha k i.val*sourceBeta k j.val)
    (a i j : ℕ) (ha : a < Nat.choose (m+1) 2)
    (hi : i < k) (hj : j < k) :
    (sourceRealizedCrossDistance P a i j)^2 =
      (sourceCrossBaseline (sourceOffset (m+1) : ℝ) k a +
        sourceAlpha k i + sourceBeta k j)^2 -
        2*sourceAlpha k i*sourceBeta k j := by
  rw [sourceRealizedCrossDistance_eq P a i j ha hi hj]
  let d := sourcePairDecode ⟨a,ha⟩
  have hspec := sourcePairDecode_spec ⟨a,ha⟩
  have h := hcross d.1 d.2 hspec.1 ⟨i,hi⟩ ⟨j,hj⟩
  simpa only [d, hspec.2] using h

/-- The already proved complete source cross spectrum now applies to the
literal point family, with no abstract distance-function hypothesis. -/
theorem source_realized_cross_pairs_separated {m k : ℕ}
    (hm : 34000 ≤ m+1) (hk : 2 ≤ k)
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (hcross : ∀ A J : Fin (m+1), A.val < J.val →
      ∀ i j : Fin k,
        dist (P (A,i)) (P (J,j))^2 =
          (sourceCrossBaseline (sourceOffset (m+1) : ℝ) k
              (sourcePairCode A J) +
            sourceAlpha k i.val + sourceBeta k j.val)^2 -
            2*sourceAlpha k i.val*sourceBeta k j.val)
    (A J C D : Fin (m+1)) (hAJ : A.val < J.val)
    (hCD : C.val < D.val) (i j u v : Fin k)
    (hneq : ¬(A=C ∧ J=D ∧ i=u ∧ j=v)) :
    1 ≤ |dist (P (A,i)) (P (J,j)) -
      dist (P (C,u)) (P (D,v))| := by
  let M := Nat.choose (m+1) 2
  let R := sourceRealizedCrossDistance P
  have hnonneg : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      0 ≤ R a i j := by
    intro a ha i hi j hj
    change 0 ≤ sourceRealizedCrossDistance P a i j
    rw [sourceRealizedCrossDistance_eq P a i j ha hi hj]
    exact dist_nonneg
  have hsq : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      (R a i j)^2 =
        (sourceCrossBaseline (sourceOffset (m+1) : ℝ) k a +
          sourceAlpha k i + sourceBeta k j)^2 -
          2*sourceAlpha k i*sourceBeta k j := by
    intro a ha i hi j hj
    exact sourceRealizedCrossDistance_square P hcross a i j ha hi hj
  have hdistinct :
      (sourcePairCode A J,i.val,j.val) ≠
        (sourcePairCode C D,u.val,v.val) := by
    intro heq
    have hc : sourcePairCode A J = sourcePairCode C D :=
      congrArg Prod.fst heq
    obtain ⟨hA,hJ⟩ := sourcePairCode_ordered_injective A J C D hAJ hCD hc
    have hi : i.val = u.val := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) heq
    have hj : j.val = v.val := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) heq
    exact hneq ⟨hA,hJ,Fin.ext hi,Fin.ext hj⟩
  have hsep := source_offset_cross_spectrum_separated R M (m+1) k
    hm hk hnonneg hsq
    (sourcePairCode A J) i.val j.val
    (sourcePairCode C D) u.val v.val
    (sourcePairCode_lt_choose A J hAJ) i.isLt j.isLt
    (sourcePairCode_lt_choose C D hCD) u.isLt v.isLt hdistinct
  simpa only [R, sourceRealizedCrossDistance_pair P A J hAJ i j,
    sourceRealizedCrossDistance_pair P C D hCD u v] using hsep

end Erdos488.Geometry.SeparatedDistances.FixedDimension
