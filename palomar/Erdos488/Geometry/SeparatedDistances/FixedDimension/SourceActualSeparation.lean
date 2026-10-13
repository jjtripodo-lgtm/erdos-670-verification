module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceActualSpectrum
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.ClusterEdgeAssembly
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourcePrime

@[expose] public section

/-! Assemble the literal local and cross metric identities into unordered
edge separation for the source construction. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

theorem source_separatedConfiguration_of_metrics {m k : ℕ}
    (hm : 34000 ≤ m+1) (hk : 2 ≤ k)
    (prime : ℕ) (hp : prime.Prime)
    (hsize : 2*(m+1)*k < prime) (hupper : prime < 4*(m+1)*k)
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (hlocal : ∀ A : Fin (m+1), ∀ i j : Fin k, i.val < j.val →
      dist (P (A,j)) (P (A,i)) =
        sourceLocalDistance prime (m+1) k
          (sourceReserve1 (m+1) k) (sourceReserve0 (m+1) k)
          A.val i.val (j.val-i.val))
    (hcross : ∀ A J : Fin (m+1), A.val < J.val →
      ∀ i j : Fin k,
        dist (P (A,i)) (P (J,j))^2 =
          (sourceCrossBaseline (sourceOffset (m+1) : ℝ) k
              (sourcePairCode A J) +
            sourceAlpha k i.val + sourceBeta k j.val)^2 -
            2*sourceAlpha k i.val*sourceBeta k j.val) :
    SeparatedConfiguration P := by
  apply separatedConfiguration_of_cluster_gaps P
  · intro A i j B u v hij huv hne
    have hne' : ¬(A.val=B.val ∧ i.val=u.val ∧
        j.val-i.val=v.val-u.val) := by
      rintro ⟨hA, hi, hδ⟩
      apply hne
      have hB : A=B := Fin.ext hA
      have hu : i=u := Fin.ext hi
      have hv : j=v := Fin.ext (by omega)
      simp [hB, hu, hv]
    have hsep := concrete_source_local_spectrum_separated prime (m+1) k
      A.val B.val i.val u.val (j.val-i.val) (v.val-u.val)
      hm hk hp hsize hupper A.isLt B.isLt (by omega) (by omega)
      (by omega) (by omega) hne'
    rw [← hlocal A i j hij, ← hlocal B u v huv] at hsep
    simpa only [dist_comm] using hsep
  · intro A B i j C D u v hAB hCD hne
    have hne' : ¬(A=C ∧ B=D ∧ i=u ∧ j=v) := by
      rintro ⟨rfl,rfl,rfl,rfl⟩
      exact hne rfl
    exact source_realized_cross_pairs_separated hm hk P hcross
      A B C D hAB hCD i j u v hne'
  · intro A i j B C u v hij hBC
    have hsq := hcross B C hBC u v
    have hgap := concrete_source_local_cross_gap
      (dist (P (B,u)) (P (C,v))) prime (m+1) k
      A.val i.val (j.val-i.val) (sourcePairCode B C) u.val v.val
      hm hk u.isLt v.isLt dist_nonneg hsq
    rw [← hlocal A i j hij] at hgap
    simpa only [dist_comm] using hgap

/-- The literal source metric has no zero-length non-diagonal edge.  This is
independent of pairwise separation of distances attached to different edges. -/
theorem source_minimum_distance_of_metrics {m k : ℕ}
    (hm : 34000 ≤ m+1) (hk : 2 ≤ k)
    (prime : ℕ) (hp : prime.Prime)
    (hsize : 2*(m+1)*k < prime) (hupper : prime < 4*(m+1)*k)
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (hlocal : ∀ A : Fin (m+1), ∀ i j : Fin k, i.val < j.val →
      dist (P (A,j)) (P (A,i)) =
        sourceLocalDistance prime (m+1) k
          (sourceReserve1 (m+1) k) (sourceReserve0 (m+1) k)
          A.val i.val (j.val-i.val))
    (hcross : ∀ A J : Fin (m+1), A.val < J.val →
      ∀ i j : Fin k,
        dist (P (A,i)) (P (J,j))^2 =
          (sourceCrossBaseline (sourceOffset (m+1) : ℝ) k
              (sourcePairCode A J) +
            sourceAlpha k i.val + sourceBeta k j.val)^2 -
            2*sourceAlpha k i.val*sourceBeta k j.val) :
    ∀ x y, x ≠ y → 1 ≤ dist (P x) (P y) := by
  apply cluster_minimum_distance P
  · intro A i j hij
    have hmin := source_local_distance_ge_one prime (m+1) k
      A.val i.val (j.val-i.val) hm hk hp.pos hsize hupper
      (by omega) (by omega)
      (sourceReserve1 (m+1) k) (sourceReserve0 (m+1) k)
    rw [← hlocal A i j hij] at hmin
    simpa only [dist_comm] using hmin
  · intro A B i j hAB
    have hsq := hcross A B hAB i j
    have hgap := concrete_source_local_cross_gap
      (dist (P (A,i)) (P (B,j))) prime (m+1) k
      A.val 0 1 (sourcePairCode A B) i.val j.val
      hm hk i.isLt j.isLt dist_nonneg hsq
    let z : Fin k := ⟨0, by omega⟩
    let o : Fin k := ⟨1, by omega⟩
    have hz : z.val = 0 := rfl
    have ho : o.val = 1 := rfl
    have h01 : z.val < o.val := by omega
    have hlocal01 := hlocal A z o h01
    rw [hz, ho, Nat.sub_zero] at hlocal01
    rw [← hlocal01] at hgap
    have hnonneg : 0 ≤ dist (P (A,o)) (P (A,z)) := dist_nonneg
    linarith

/-- The independent minimum-distance statement makes the literal metric
configuration injective. -/
theorem source_injective_of_metrics {m k : ℕ}
    (hm : 34000 ≤ m+1) (hk : 2 ≤ k)
    (prime : ℕ) (hp : prime.Prime)
    (hsize : 2*(m+1)*k < prime) (hupper : prime < 4*(m+1)*k)
    (P : Fin (m+1) × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin m) (m+1)))
    (hlocal : ∀ A : Fin (m+1), ∀ i j : Fin k, i.val < j.val →
      dist (P (A,j)) (P (A,i)) =
        sourceLocalDistance prime (m+1) k
          (sourceReserve1 (m+1) k) (sourceReserve0 (m+1) k)
          A.val i.val (j.val-i.val))
    (hcross : ∀ A J : Fin (m+1), A.val < J.val →
      ∀ i j : Fin k,
        dist (P (A,i)) (P (J,j))^2 =
          (sourceCrossBaseline (sourceOffset (m+1) : ℝ) k
              (sourcePairCode A J) +
            sourceAlpha k i.val + sourceBeta k j.val)^2 -
            2*sourceAlpha k i.val*sourceBeta k j.val) :
    Function.Injective P :=
  injective_of_unit_minimum_distance P
    (source_minimum_distance_of_metrics hm hk prime hp hsize hupper P hlocal hcross)

/-- A prime and the actual source metric construction yield a fully
unit-separated finite configuration. The diameter and fixed ambient-dimension
bound are further obligations. -/
theorem source_actual_separated_configuration_exists {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k) :
    ∃ P : Fin (n+2) × Fin k →
        EuclideanSpace ℝ (ClusterCoordinate (Fin (n+1)) (n+2)),
      SeparatedConfiguration P := by
  obtain ⟨prime, hp, hsize, hupper⟩ :=
    source_ruler_prime_exists (n+2) k (by omega) (by omega)
  obtain ⟨P, hlocal, hcross⟩ :=
    source_actual_ruler_configuration_metrics hm hk prime
  exact ⟨P, source_separatedConfiguration_of_metrics hm hk prime hp
    hsize hupper P hlocal hcross⟩

/-- A single actual source configuration has separated edge distances,
minimum nonzero distance one, and distinct vertices. -/
theorem source_actual_separated_injective_configuration_exists {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k) :
    ∃ P : Fin (n+2) × Fin k →
        EuclideanSpace ℝ (ClusterCoordinate (Fin (n+1)) (n+2)),
      SeparatedConfiguration P ∧
      (∀ x y, x ≠ y → 1 ≤ dist (P x) (P y)) ∧
      Function.Injective P := by
  obtain ⟨prime, hp, hsize, hupper⟩ :=
    source_ruler_prime_exists (n+2) k (by omega) (by omega)
  obtain ⟨P, hlocal, hcross⟩ :=
    source_actual_ruler_configuration_metrics hm hk prime
  refine ⟨P, source_separatedConfiguration_of_metrics hm hk prime hp
    hsize hupper P hlocal hcross, ?_, ?_⟩
  · exact source_minimum_distance_of_metrics hm hk prime hp
      hsize hupper P hlocal hcross
  · exact source_injective_of_metrics hm hk prime hp
      hsize hupper P hlocal hcross

end Erdos488.Geometry.SeparatedDistances.FixedDimension
