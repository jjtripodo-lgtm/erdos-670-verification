module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceMixedBands

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Algebraically normalized squares of the source's constant/second-harmonic reserves. -/
noncomputable def sourceReserve0Sq (m k : ℕ) : ℝ :=
  3888*(m : ℝ)^2*(k : ℝ)^4/(sourceOffset m : ℝ)^2
/-- Algebraically normalized square of the source's first-harmonic reserve. -/
noncomputable def sourceReserve1Sq (m k : ℕ) : ℝ :=
  (21168*(9/8 : ℝ)^4*32)*(k : ℝ)^4*((sourceOffset m : ℝ)+(m : ℝ))

theorem sourceOffset_plus_m_upper (m : ℕ) (hm : 34000 ≤ m) :
    (sourceOffset m : ℝ)+(m : ℝ) ≤ (m : ℝ)^2/63 := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hnonneg : 0 ≤ (m : ℝ)*((m : ℝ)-1)/64 := by
    apply div_nonneg (mul_nonneg (by positivity) (by linarith)) (by norm_num)
  have hceil := Nat.ceil_lt_add_one hnonneg
  change (sourceOffset m : ℝ) < (m : ℝ)*((m : ℝ)-1)/64+1 at hceil
  have hmsq : (34000 : ℝ)*m ≤ (m : ℝ)^2 := by nlinarith
  nlinarith

theorem sourceReserve0Sq_bound (m k : ℕ) (hm : 34000 ≤ m) :
    sourceReserve0Sq m k ≤ (972/25 : ℝ)*(m : ℝ)^2*(k : ℝ)^4 := by
  have hK := sourceOffset_lower m hm
  have hKpos : (0 : ℝ) < sourceOffset m := by linarith
  have hKsq : (100 : ℝ) ≤ (sourceOffset m : ℝ)^2 := by nlinarith
  have hmulp := mul_le_mul_of_nonneg_left hKsq
    (show 0 ≤ (972/25 : ℝ)*(m : ℝ)^2*(k : ℝ)^4 by positivity)
  unfold sourceReserve0Sq
  apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
  nlinarith

theorem sourceReserve1Sq_bound (m k : ℕ) (hm : 34000 ≤ m) :
    sourceReserve1Sq m k ≤ (137781/8 : ℝ)*(m : ℝ)^2*(k : ℝ)^4 := by
  have h := mul_le_mul_of_nonneg_left (sourceOffset_plus_m_upper m hm)
    (show 0 ≤ (21168*(9/8 : ℝ)^4*32)*(k : ℝ)^4 by positivity)
  unfold sourceReserve1Sq
  nlinarith

/-- The full T² reserve fits strictly inside the chosen radius square. -/
theorem source_total_reserve_bound (m k : ℕ) (hm : 34000 ≤ m) :
    2*sourceReserve0Sq m k+sourceReserve1Sq m k ≤ (sourceRadius m k)^2 := by
  have h₀ := sourceReserve0Sq_bound m k hm
  have h₁ := sourceReserve1Sq_bound m k hm
  rw [sourceRadius_square]
  nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (show 0 ≤ (k : ℝ)^4 by positivity)]

/-- The actual source harmonic reserves satisfy the complete local slope budget. -/
theorem source_harmonic_reserve_bound (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    (sourceTheta k)^2*(sourceReserve1Sq m k+4*sourceReserve0Sq m k) ≤
      600*(m : ℝ)^2*(k : ℝ)^2 := by
  have h₀ := mul_le_mul_of_nonneg_left (sourceReserve0Sq_bound m k hm) (sq_nonneg (sourceTheta k))
  have h₁ := mul_le_mul_of_nonneg_left (sourceReserve1Sq_bound m k hm) (sq_nonneg (sourceTheta k))
  have hs : (sourceTheta k)^2*(k : ℝ)^2=1/32 := source_theta_scale k (by omega)
  have hmul := congrArg (fun x : ℝ => x*(m : ℝ)^2*(k : ℝ)^2) hs
  have hn : 0 ≤ (m : ℝ)^2*(k : ℝ)^2 := by positivity
  nlinarith

/-- The normalized first reserve is literally the source's original operator expression. -/
theorem sourceReserve1Sq_eq_operator_formula (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    sourceReserve1Sq m k =
      3*(84*(9/8 : ℝ)*((9/8)*(k : ℝ))*
        Real.sqrt ((sourceOffset m : ℝ)+(m : ℝ))/sourceTheta k)^2 := by
  have hK := sourceOffset_lower m hm
  have hm' : (0 : ℝ) ≤ m := by positivity
  have hsqrt := Real.sq_sqrt (show 0 ≤ (sourceOffset m : ℝ)+(m : ℝ) by positivity)
  have hθ : sourceTheta k ≠ 0 := (sourceTheta_pos k (by omega)).ne'
  have hs : (sourceTheta k)^2*(k : ℝ)^2=1/32 := source_theta_scale k (by omega)
  rw [div_pow,← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero 2 hθ)).2
  unfold sourceReserve1Sq
  simp only [mul_pow,hsqrt]
  have hmul := congrArg (fun x : ℝ => x*(k : ℝ)^2*((sourceOffset m : ℝ)+(m : ℝ))) hs
  nlinarith only [hmul]

/-- The constant/second-harmonic reserve agrees with the original source formula. -/
theorem sourceReserve0Sq_eq_original (m k : ℕ) :
    sourceReserve0Sq m k = 3*(m : ℝ)*
      ((m : ℝ)*(9/8 : ℝ)^2*(k : ℝ)^4/((1/32 : ℝ)^2*(sourceOffset m : ℝ)^2)) := by
  unfold sourceReserve0Sq
  ring

noncomputable def sourceReserve0 (m k : ℕ) : ℝ := Real.sqrt (sourceReserve0Sq m k)
noncomputable def sourceReserve1 (m k : ℕ) : ℝ := Real.sqrt (sourceReserve1Sq m k)

theorem sourceReserve0_square (m k : ℕ) : (sourceReserve0 m k)^2=sourceReserve0Sq m k := by
  apply Real.sq_sqrt
  unfold sourceReserve0Sq
  positivity

theorem sourceReserve1_square (m k : ℕ) : (sourceReserve1 m k)^2=sourceReserve1Sq m k := by
  apply Real.sq_sqrt
  unfold sourceReserve1Sq
  positivity

/-- All local spectrum scalar hypotheses are now discharged for the literal source reserves. -/
theorem concrete_source_local_spectrum_separated (p m k A B i j δ ε : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hp : p.Prime)
    (hsize : 2*m*k < p) (hupper : p < 4*m*k)
    (hA : A < m) (hB : B < m) (hδ : 0 < δ) (hε : 0 < ε)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬(A=B ∧ i=j ∧ δ=ε)) :
    1 ≤ |sourceLocalDistance p m k (sourceReserve1 m k) (sourceReserve0 m k) A i δ-
      sourceLocalDistance p m k (sourceReserve1 m k) (sourceReserve0 m k) B j ε| := by
  apply source_local_spectrum_separated p m k A B i j δ ε hm hk hp hsize hupper
    hA hB hδ hε hi hj hne
  rw [sourceReserve1_square,sourceReserve0_square]
  exact source_harmonic_reserve_bound m k hm hk

/-- The source reserves also discharge the local/cross radius reserve. -/
theorem concrete_source_local_cross_gap (D : ℝ) (p m k A l δ a i j : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hi : i < k) (hj : j < k) (hD : 0 ≤ D)
    (hsq : D^2=(sourceCrossBaseline (sourceOffset m) k a+sourceAlpha k i+sourceBeta k j)^2-
      2*sourceAlpha k i*sourceBeta k j) :
    1 ≤ D-sourceLocalDistance p m k (sourceReserve1 m k) (sourceReserve0 m k) A l δ := by
  apply source_local_cross_gap D (sourceReserve1 m k) (sourceReserve0 m k)
    p m k A l δ a i j hm hk hi hj hD hsq
  rw [sourceReserve1_square,sourceReserve0_square]
  have h := source_total_reserve_bound m k hm
  have h₀ : 0 ≤ sourceReserve0Sq m k := by unfold sourceReserve0Sq; positivity
  linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
