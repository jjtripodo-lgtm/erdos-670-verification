module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceActualCrossMetric
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceReserveBudgets

@[expose] public section

/-! A diameter bound for the literal point family produced by the source
operator. The theorem uses its local and cross metric identities; it assumes
no diameter or separation property of the points. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The nominal largest colex block plus the literal perturbation and metric
error is a cap on every distance of one actual source configuration. -/
theorem source_diameter_of_metrics {m k : ℕ}
    (hm : 34000 ≤ m+1) (hk : 2 ≤ k) (prime : ℕ)
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
            2*sourceAlpha k i.val*sourceBeta k j.val)
    (x y : Fin (m+1) × Fin k) :
    dist (P x) (P y) ≤
      sourceMacroStep (k : ℝ) *
        ((sourceOffset (m+1) : ℝ) + (Nat.choose (m+1) 2 : ℝ)) +
      sourcePerturbationBound (k : ℝ) +
      sourceError (sourceOffset (m+1) : ℝ) (k : ℝ) := by
  let K : ℝ := sourceOffset (m+1)
  let S : ℝ := sourceMacroStep (k : ℝ)
  let A : ℝ := sourcePerturbationBound (k : ℝ)
  let E : ℝ := sourceError K (k : ℝ)
  let M : ℕ := Nat.choose (m+1) 2
  have hm₀ : 34000 ≤ m+1 := hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (72247875/4 : ℝ) ≤ K := sourceOffset_lower (m+1) hm
  have hS : 0 ≤ S := by dsimp [S, sourceMacroStep]; positivity
  have hA : 0 ≤ A := by
    dsimp [A, sourcePerturbationBound]
    have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    positivity
  have hE : 0 ≤ E := by
    dsimp [E, sourceError]
    have ht := source_Tmin_pos K k hK hk'
    positivity
  have hM : 1 ≤ M := by
    dsimp [M]
    have h : Nat.choose 2 2 ≤ Nat.choose (m+1) 2 :=
      Nat.choose_le_choose 2 (by omega)
    simpa using h
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlocalcap (B : Fin (m+1)) (i j : Fin k) (hij : i.val < j.val) :
      dist (P (B,i)) (P (B,j)) ≤ S*(K+(M : ℝ))+A+E := by
    have hreserve : (sourceReserve1 (m+1) k)^2 +
        (sourceReserve0 (m+1) k)^2 ≤ (sourceRadius (m+1) k)^2 := by
      rw [sourceReserve1_square, sourceReserve0_square]
      have htotal := source_total_reserve_bound (m+1) k hm
      have hzero : 0 ≤ sourceReserve0Sq (m+1) k := by
        unfold sourceReserve0Sq
        positivity
      linarith
    have hR : 0 ≤ sourceRadius (m+1) k := by
      unfold sourceRadius
      positivity
    have hloc := localDistanceModel_le_three_radius
      (sourceRadius (m+1) k) (sourceTheta k)
      (sourceReserve1 (m+1) k) (sourceReserve0 (m+1) k)
      ((j.val-i.val : ℕ) : ℝ) (rulerArc prime k B.val i.val (j.val-i.val))
      hR hreserve
    have hgap := source_mixed_scalar_budget (m+1) k hm hk
    have hbase : sourceBaseline K k = S*(K+1) := rfl
    have hT : sourceTmin K k = sourceBaseline K k - A := rfl
    rw [dist_comm, hlocal B i j hij]
    change sourceLocalDistance prime (m+1) k
      (sourceReserve1 (m+1) k) (sourceReserve0 (m+1) k)
      B.val i.val (j.val-i.val) ≤ _
    have hloc' : sourceLocalDistance prime (m+1) k
        (sourceReserve1 (m+1) k) (sourceReserve0 (m+1) k)
        B.val i.val (j.val-i.val) ≤ 3*sourceRadius (m+1) k := by
      simpa only [sourceLocalDistance] using hloc
    rw [hT, hbase] at hgap
    have hstep : S*(K+1) ≤ S*(K+(M : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hS
    linarith
  have hcrosscap (B C : Fin (m+1)) (hBC : B.val < C.val)
      (i j : Fin k) :
      dist (P (B,i)) (P (C,j)) ≤ S*(K+(M : ℝ))+A+E := by
    have hsq := hcross B C hBC i j
    have herr := source_cross_error
      (dist (P (B,i)) (P (C,j))) K k (sourcePairCode B C)
      i.val j.val hK hk i.isLt j.isLt dist_nonneg hsq
    have hpert := source_digit_sum_bound k i.val j.val hk i.isLt j.isLt
    have hcode := sourcePairCode_lt_choose B C hBC
    have hcode' : (sourcePairCode B C : ℝ) ≤ (M : ℝ) - 1 := by
      have hnat : sourcePairCode B C ≤ M-1 := by omega
      exact_mod_cast hnat
    have hbase : sourceCrossBaseline K k (sourcePairCode B C) =
        S*(K+1+(sourcePairCode B C : ℝ)) := by
      dsimp [sourceCrossBaseline, sourceBaseline, S]
      ring
    have hmul := mul_le_mul_of_nonneg_left hcode' hS
    obtain ⟨herr₀, herr₁⟩ := abs_le.mp herr
    obtain ⟨hpert₀, hpert₁⟩ := abs_le.mp hpert
    dsimp [E, A] at *
    rw [hbase] at herr₁
    linarith
  rcases x with ⟨B,i⟩
  rcases y with ⟨C,j⟩
  rcases lt_trichotomy B.val C.val with hxy | hsame | hyx
  · simpa only [K, S, A, E, M] using hcrosscap B C hxy i j
  · have hB : B = C := Fin.ext hsame
    subst C
    rcases lt_trichotomy i.val j.val with hij | heq | hji
    · simpa only [K, S, A, E, M] using hlocalcap B i j hij
    · have hi : i = j := Fin.ext heq
      subst j
      have hcap : 0 ≤ S*(K+(M : ℝ))+A+E := by positivity
      simpa using hcap
    · have h := hlocalcap B j i hji
      simpa only [dist_comm, K, S, A, E, M] using h
  · have h := hcrosscap C B hyx j i
    simpa only [dist_comm, K, S, A, E, M] using h

/-- The source operator supplies one literal finite point family with both
exact edge metrics and the global diameter cap. -/
theorem source_actual_ruler_configuration_metrics_diameter {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k) (prime : ℕ) :
    ∃ P : Fin (n+2) × Fin k →
        EuclideanSpace ℝ (ClusterCoordinate (Fin (n+1)) (n+2)),
      (∀ A : Fin (n+2), ∀ i j : Fin k, i.val < j.val →
        dist (P (A,j)) (P (A,i)) =
          sourceLocalDistance prime (n+2) k
            (sourceReserve1 (n+2) k) (sourceReserve0 (n+2) k)
            A.val i.val (j.val-i.val)) ∧
      (∀ A J : Fin (n+2), A.val < J.val →
        ∀ i j : Fin k,
          dist (P (A,i)) (P (J,j))^2 =
            (sourceCrossBaseline (sourceOffset (n+2) : ℝ) k
                (sourcePairCode A J) +
              sourceAlpha k i.val + sourceBeta k j.val)^2 -
              2*sourceAlpha k i.val*sourceBeta k j.val) ∧
      (∀ x y : Fin (n+2) × Fin k,
        dist (P x) (P y) ≤
          sourceMacroStep (k : ℝ) *
            ((sourceOffset (n+2) : ℝ) +
              (Nat.choose (n+2) 2 : ℝ)) +
          sourcePerturbationBound (k : ℝ) +
          sourceError (sourceOffset (n+2) : ℝ) (k : ℝ)) := by
  obtain ⟨P, hlocal, hcross⟩ :=
    source_actual_ruler_configuration_metrics hm hk prime
  exact ⟨P, hlocal, hcross,
    fun x y => source_diameter_of_metrics hm hk prime P hlocal hcross x y⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension
