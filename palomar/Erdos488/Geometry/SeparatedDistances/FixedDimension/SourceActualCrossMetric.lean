module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceQuadraticMatrix
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.GeometricLocalSeparation

@[expose] public section

/-! Connecting the source's actual colex macro realization and three-slot
operator to the cross-cluster squared-distance identity. -/

open scoped BigOperators Matrix
open Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Zero-based code of an ordered macro edge. -/
def sourcePairCode {m : ℕ} (A J : Fin (m+1)) : ℕ :=
  Nat.choose J.val 2 + A.val

theorem sourcePairCode_lt_choose {m : ℕ} (A J : Fin (m+1))
    (hAJ : A.val < J.val) :
    sourcePairCode A J < Nat.choose (m+1) 2 := by
  have hstep : Nat.choose (J.val+1) 2 =
      Nat.choose J.val 2 + J.val := by
    rw [Nat.choose_succ_succ]
    simp [Nat.choose_one_right, add_comm]
  have hchoose : Nat.choose (J.val+1) 2 ≤ Nat.choose (m+1) 2 :=
    Nat.choose_le_choose 2 (by omega)
  dsimp [sourcePairCode]
  omega

theorem sourcePairCode_ordered_injective {m : ℕ}
    (A J C D : Fin (m+1))
    (hAJ : A.val < J.val) (hCD : C.val < D.val)
    (heq : sourcePairCode A J = sourcePairCode C D) :
    A = C ∧ J = D := by
  have hJA : sourcePairCode A J < Nat.choose (J.val+1) 2 := by
    have hstep : Nat.choose (J.val+1) 2 =
        Nat.choose J.val 2 + J.val := by
      rw [Nat.choose_succ_succ]
      simp [Nat.choose_one_right, add_comm]
    dsimp [sourcePairCode]
    omega
  have hDC : sourcePairCode C D < Nat.choose (D.val+1) 2 := by
    have hstep : Nat.choose (D.val+1) 2 =
        Nat.choose D.val 2 + D.val := by
      rw [Nat.choose_succ_succ]
      simp [Nat.choose_one_right, add_comm]
    dsimp [sourcePairCode]
    omega
  have hJ : J.val = D.val := by
    rcases lt_trichotomy J.val D.val with h | h | h
    · have hchoose : Nat.choose (J.val+1) 2 ≤ Nat.choose D.val 2 :=
        Nat.choose_le_choose 2 (by omega)
      dsimp [sourcePairCode] at heq hJA
      omega
    · exact h
    · have hchoose : Nat.choose (D.val+1) 2 ≤ Nat.choose J.val 2 :=
        Nat.choose_le_choose 2 (by omega)
      dsimp [sourcePairCode] at heq hDC
      omega
  have hA : A.val = C.val := by
    dsimp [sourcePairCode] at heq
    rw [hJ] at heq
    omega
  exact ⟨Fin.ext hA, Fin.ext hJ⟩

theorem sourcePairCode_surjective {m : ℕ} (a : ℕ)
    (ha : a < Nat.choose (m+1) 2) :
    ∃ A J : Fin (m+1), A.val < J.val ∧ sourcePairCode A J = a := by
  have hmem : a+1 ∈ Finset.Icc 1 (Nat.choose (m+1) 2) := by
    simp only [Finset.mem_Icc]
    omega
  rw [← colexLabel_range_exact] at hmem
  obtain ⟨j, hj, hmemj⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmemj
  have hj' : j < m+1 := Finset.mem_range.mp hj
  have hi' : i < j := Finset.mem_range.mp hi
  refine ⟨⟨i, by omega⟩, ⟨j, hj'⟩, hi', ?_⟩
  dsimp [sourcePairCode]
  simp only [colexLabel] at heq
  omega

theorem sourceCrossBaseline_pairCode {m : ℕ} (K : ℝ) (k : ℕ)
    (A J : Fin (m+1)) (hAJ : A.val < J.val) :
    sourceCrossBaseline K k (sourcePairCode A J) =
      sourceMacroStep (k : ℝ) * colexDistance K A J := by
  simp [sourceCrossBaseline, sourceBaseline, sourcePairCode,
    colexDistance, hAJ, colexLabel, Nat.cast_add]
  ring

/-- The off-diagonal flattening is canceled exactly by the private radius. -/
theorem source_macro_base_square {m k : ℕ} (hk : 0 < k)
    (K : ℝ) (p : Fin (m+1) → EuclideanSpace ℝ (Fin m))
    (hpd : ∀ i j,
      ‖p j-p i‖ ^ 2 =
        offDiagonalShift (colexSqData (m:=m) K)
          (sourceFlatteningRadius (m+1) k) i j)
    (A J : Fin (m+1)) (hAJ : A ≠ J) :
    (sourceMacroStep (k : ℝ)) ^ 2 *
      (∑ q : Fin m, ((p A-p J) q)^2) +
      4 * (sourceRadius (m+1) k)^2 =
      (sourceMacroStep (k : ℝ) * colexDistance K A J)^2 := by
  have hnorm := hpd J A
  rw [EuclideanSpace.real_norm_sq_eq] at hnorm
  have hne : J ≠ A := Ne.symm hAJ
  simp only [offDiagonalShift, if_neg hne, colexSqData,
    colexDistance_symm K J A] at hnorm
  have hS : sourceMacroStep (k : ℝ) ≠ 0 := by
    unfold sourceMacroStep
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    positivity
  have hr : (sourceMacroStep (k : ℝ))^2 *
      sourceFlatteningRadius (m+1) k =
      2 * (sourceRadius (m+1) k)^2 := by
    unfold sourceFlatteningRadius
    field_simp
  nlinarith [hnorm, hr]

/-- The source coefficients, macro flattening, and residual Gram factor give
the exact corrected cross metric for the literal Euclidean cluster points. -/
theorem source_clusterPoint_cross_metric_square {m k : ℕ} (hk : 0 < k)
    (K : ℝ) (p : Fin (m+1) → EuclideanSpace ℝ (Fin m))
    (B : Fin (m+1) → EuclideanSpace ℝ (Fin m))
    (F G : Fin m → EuclideanSpace ℝ (Fin m))
    (V : Matrix (Fin (m+1) × Fin 5) (Fin (m+1) × Fin 5) ℝ)
    (hpd : ∀ i j,
      ‖p j-p i‖ ^ 2 =
        offDiagonalShift (colexSqData (m:=m) K)
          (sourceFlatteningRadius (m+1) k) i j)
    (hB : ∀ A J, inner ℝ (p A-p J) (B A) =
      sourceQuadraticPotential k A J)
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence m K i a)
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence m K i a)
    (b₀ b₁ : ℝ)
    (hfactor : (sourceActiveMatrix k B F G)ᵀ *
        (sourceActiveMatrix k B F G) + Vᵀ * V =
        Matrix.diagonal (fun q : Fin (m+1) × Fin 5 =>
          trigWeight b₀ b₁ b₀ q.2))
    (hreserve : 2*b₀^2+b₁^2 ≤ (sourceRadius (m+1) k)^2)
    (A J : Fin (m+1)) (hAJ : A.val < J.val)
    (i j : ℕ) (yi yj : ℝ) :
    let R := sourceRadius (m+1) k
    let axis := Real.sqrt (R^2-(2*b₀^2+b₁^2))
    let z (t : ℕ) := sourceTheta k * ((t : ℝ)-((k : ℝ)-1)/2)
    dist (clusterPoint (fun A q => p A q) (sourceActiveMatrix k B F G)
        V (sourceMacroStep (k : ℝ)) R axis A (z i) yi)
      (clusterPoint (fun A q => p A q) (sourceActiveMatrix k B F G)
        V (sourceMacroStep (k : ℝ)) R axis J (z j) yj)^2 =
      (sourceCrossBaseline K k (sourcePairCode A J) +
        sourceAlpha k i + sourceBeta k j)^2 -
        2*sourceAlpha k i*sourceBeta k j := by
  dsimp only
  have hne : A ≠ J := Fin.ne_of_lt hAJ
  have haxis :
      (Real.sqrt ((sourceRadius (m+1) k)^2-(2*b₀^2+b₁^2)))^2 =
      (sourceRadius (m+1) k)^2-(b₀^2+b₁^2+b₀^2) := by
    rw [Real.sq_sqrt (by linarith :
      0 ≤ (sourceRadius (m+1) k)^2-(2*b₀^2+b₁^2))]
    ring
  have hbase :
      (sourceMacroStep (k : ℝ))^2 *
        (∑ q : Fin m, (p A q-p J q)^2) +
        4*(sourceRadius (m+1) k)^2 =
      (sourceCrossBaseline K k (sourcePairCode A J))^2 := by
    rw [sourceCrossBaseline_pairCode K k A J hAJ]
    simpa only [WithLp.ofLp_sub, Pi.sub_apply] using
      source_macro_base_square hk K p hpd A J hne
  have hprojA := sourceActiveMatrix_forward_projection_metric K k hk
    p B F G hB hF hG A J hAJ i
  have hprojB := sourceActiveMatrix_reverse_projection_metric K k hk
    p B F G hB hF hG J A hAJ j
  have hprojA' :
      2 * sourceMacroStep (k : ℝ) *
        ((fun q => p A q-p J q) ⬝ᵥ
          (sourceActiveMatrix k B F G *ᵥ clusteredFeature A
            (sourceTheta k * ((i : ℝ)-((k : ℝ)-1)/2)))) =
      2 * sourceCrossBaseline K k (sourcePairCode A J) *
        sourceAlpha k i + (sourceAlpha k i)^2 := by
    rw [sourceCrossBaseline_pairCode K k A J hAJ]
    simpa only [WithLp.ofLp_sub, Pi.sub_apply, mul_assoc] using hprojA
  have hprojB' :
      -2 * sourceMacroStep (k : ℝ) *
        ((fun q => p A q-p J q) ⬝ᵥ
          (sourceActiveMatrix k B F G *ᵥ clusteredFeature J
            (sourceTheta k * ((j : ℝ)-((k : ℝ)-1)/2)))) =
      2 * sourceCrossBaseline K k (sourcePairCode A J) *
        sourceBeta k j + (sourceBeta k j)^2 := by
    rw [sourceCrossBaseline_pairCode K k A J hAJ,
      colexDistance_symm K A J]
    have hswap : ∀ q : Fin m, (p J-p A) q = -(p A-p J) q := by
      intro q
      simp only [WithLp.ofLp_sub, Pi.sub_apply]
      ring
    simp_rw [hswap] at hprojB
    simpa only [WithLp.ofLp_sub, Pi.sub_apply, dotProduct,
      neg_mul, Finset.sum_neg_distrib, mul_neg, neg_mul] using hprojB
  exact clusterPoint_cross_metric_square (fun A q => p A q)
    (sourceActiveMatrix k B F G) V
    (sourceMacroStep (k : ℝ)) (sourceRadius (m+1) k)
    (Real.sqrt ((sourceRadius (m+1) k)^2-(2*b₀^2+b₁^2)))
    b₀ b₁ b₀
    (sourceCrossBaseline K k (sourcePairCode A J))
    (sourceAlpha k i) (sourceBeta k j)
    hfactor A J hne _ _ yi yj haxis hbase hprojA' hprojB'

/-- The universal source operator now produces actual Euclidean ruler points
whose cross distances obey the corrected square formula. This theorem does
not yet assert pairwise separation or the final diameter bound. -/
theorem source_actual_ruler_configuration_cross_square {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k) (prime : ℕ) :
    ∃ P : Fin (n+2) × Fin k →
        EuclideanSpace ℝ (ClusterCoordinate (Fin (n+1)) (n+2)),
      ∀ A J : Fin (n+2), A.val < J.val →
      ∀ i j : Fin k,
        dist (P (A,i)) (P (J,j))^2 =
          (sourceCrossBaseline (sourceOffset (n+2) : ℝ) k
              (sourcePairCode A J) +
            sourceAlpha k i.val + sourceBeta k j.val)^2 -
            2*sourceAlpha k i.val*sourceBeta k j.val := by
  obtain ⟨p, B, F, G, V, hpd, hB, hF, hG, hfactor⟩ :=
    source_actual_operator_completion_universal_B_matrix hm hk
  let R := sourceRadius (n+2) k
  let b₀ := sourceReserve0 (n+2) k
  let b₁ := sourceReserve1 (n+2) k
  let axis := Real.sqrt (R^2-(2*b₀^2+b₁^2))
  let P : Fin (n+2) × Fin k →
      EuclideanSpace ℝ (ClusterCoordinate (Fin (n+1)) (n+2)) :=
    fun q => rulerPoint (fun A t => p A t)
      (sourceActiveMatrix k B F G) V
      (sourceMacroStep (k : ℝ)) R axis (sourceTheta k)
      (((k : ℝ)-1)/2) prime k q.1 q.2.val
  refine ⟨P, ?_⟩
  intro A J hAJ i j
  have hreserve : 2*b₀^2+b₁^2 ≤ R^2 := by
    dsimp [b₀, b₁, R]
    rw [sourceReserve0_square, sourceReserve1_square]
    exact source_total_reserve_bound (n+2) k hm
  change dist
    (clusterPoint (fun A t => p A t) (sourceActiveMatrix k B F G) V
      (sourceMacroStep (k : ℝ)) R axis A
      (sourceTheta k * ((i.val : ℝ)-((k : ℝ)-1)/2))
      (3*(primeRuler prime k A.val i.val : ℝ)))
    (clusterPoint (fun A t => p A t) (sourceActiveMatrix k B F G) V
      (sourceMacroStep (k : ℝ)) R axis J
      (sourceTheta k * ((j.val : ℝ)-((k : ℝ)-1)/2))
      (3*(primeRuler prime k J.val j.val : ℝ))) ^ 2 = _
  exact source_clusterPoint_cross_metric_square (by omega) _ p B F G V
    hpd hB hF hG b₀ b₁ hfactor hreserve A J hAJ
    i.val j.val
    (3*(primeRuler prime k A.val i.val : ℝ))
    (3*(primeRuler prime k J.val j.val : ℝ))

/-- Local ruler distances and corrected cross squares hold for one and the
same actual finite configuration. -/
theorem source_actual_ruler_configuration_metrics {n k : ℕ}
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
              2*sourceAlpha k i.val*sourceBeta k j.val) := by
  obtain ⟨p, B, F, G, V, hpd, hB, hF, hG, hfactor⟩ :=
    source_actual_operator_completion_universal_B_matrix hm hk
  let R := sourceRadius (n+2) k
  let b₀ := sourceReserve0 (n+2) k
  let b₁ := sourceReserve1 (n+2) k
  let axis := Real.sqrt (R^2-(2*b₀^2+b₁^2))
  let P : Fin (n+2) × Fin k →
      EuclideanSpace ℝ (ClusterCoordinate (Fin (n+1)) (n+2)) :=
    fun q => rulerPoint (fun A t => p A t)
      (sourceActiveMatrix k B F G) V
      (sourceMacroStep (k : ℝ)) R axis (sourceTheta k)
      (((k : ℝ)-1)/2) prime k q.1 q.2.val
  refine ⟨P, ?_, ?_⟩
  · intro A i j hij
    have hR : R ≠ 0 :=
      (sourceRadius_pos (n+2) k (by omega) (by omega)).ne'
    have hdist := rulerPoint_local_distance (fun A t => p A t)
      (sourceActiveMatrix k B F G) V
      (sourceMacroStep (k : ℝ)) R axis (sourceTheta k)
      (((k : ℝ)-1)/2) b₀ b₁ b₀ prime k A i.val
      (j.val-i.val) hR hfactor
    have hsum : i.val+(j.val-i.val)=j.val := by omega
    simpa only [P, hsum, sourceLocalDistance, R, b₀, b₁] using hdist
  · intro A J hAJ i j
    have hreserve : 2*b₀^2+b₁^2 ≤ R^2 := by
      dsimp [b₀, b₁, R]
      rw [sourceReserve0_square, sourceReserve1_square]
      exact source_total_reserve_bound (n+2) k hm
    change dist
      (clusterPoint (fun A t => p A t) (sourceActiveMatrix k B F G) V
        (sourceMacroStep (k : ℝ)) R axis A
        (sourceTheta k * ((i.val : ℝ)-((k : ℝ)-1)/2))
        (3*(primeRuler prime k A.val i.val : ℝ)))
      (clusterPoint (fun A t => p A t) (sourceActiveMatrix k B F G) V
        (sourceMacroStep (k : ℝ)) R axis J
        (sourceTheta k * ((j.val : ℝ)-((k : ℝ)-1)/2))
        (3*(primeRuler prime k J.val j.val : ℝ))) ^ 2 = _
    exact source_clusterPoint_cross_metric_square (by omega) _ p B F G V
      hpd hB hF hG b₀ b₁ hfactor hreserve A J hAJ
      i.val j.val
      (3*(primeRuler prime k A.val i.val : ℝ))
      (3*(primeRuler prime k J.val j.val : ℝ))

end Erdos488.Geometry.SeparatedDistances.FixedDimension
