module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRulerSeparation
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.HarmonicLocalModel

@[expose] public section

/-! All local ruler-distance models, across every cluster and lag, are separated.
Only explicit scalar guards remain; no local-separation hypothesis is assumed. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def rulerArc (p k A i δ : ℕ) : ℝ := 3*(primeRulerGap p k A i δ : ℝ)

/-- One universal arc ceiling, exploiting the actual endpoint constraint i+δ<k. -/
theorem rulerArc_upper (p k A i δ : ℕ) (hp : 0 < p) (hi : i+δ < k) :
    rulerArc p k A i δ ≤ 12*(p : ℝ)*k := by
  have h := (primeRulerGap_window p k A i δ hp).2
  have hr : (primeRulerGap p k A i δ : ℝ) < (4*(δ : ℝ)+1)*p := by exact_mod_cast h
  have hδ : (δ : ℝ)+1 ≤ k := by exact_mod_cast (show δ+1 ≤ k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold rulerArc
  nlinarith

/-- The source's lower arc estimate 3tpδ for t=3. -/
theorem rulerArc_lower (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ) :
    9*(p : ℝ)*δ ≤ rulerArc p k A i δ := by
  have h := (primeRulerGap_linear_bounds p k A i δ hp hδ).1
  have hr : 3*(p : ℝ)*δ < (primeRulerGap p k A i δ : ℝ) := by exact_mod_cast h
  unfold rulerArc
  linarith

/-- Increasing arcs cannot come from decreasing lag bands. -/
theorem rulerArc_order_forces_lag_order (p k A B i j δ ε : ℕ) (hp : 0 < p)
    (h : rulerArc p k A i δ ≤ rulerArc p k B j ε) : δ ≤ ε := by
  by_contra hnot
  have hh := primeRulerGap_different_lag p k B A j i ε δ hp (by omega)
  have hr : 2*(p : ℝ) < (primeRulerGap p k A i δ : ℝ)-(primeRulerGap p k B j ε : ℝ) := by
    exact_mod_cast hh
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold rulerArc at h
  linarith

/-- Exhaustive local/local separation for the explicit ruler and two harmonics.
Distinct triples represent distinct local unordered pairs. The proof handles
same-lag and different-lag cases without assuming their distance separation. -/
theorem local_ruler_model_separated (p m k A B i j δ ε : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬ (A=B ∧ i=j ∧ δ=ε))
    (R Y θ b₁ b₂ J : ℝ) (hR : 0 < R) (hY : 12*(p : ℝ)*k ≤ Y)
    (hangle : Y/(2*R) ≤ Real.pi) (hγ : 0 < Real.cos (Y/(2*R)))
    (hθ : 0 ≤ θ) (hfeature : θ*k ≤ Real.pi/2) (hJ : 0 ≤ J)
    (hJbound : θ^2*(b₁^2+4*b₂^2) ≤ J^2)
    (hguard : 1 ≤ 3*(Real.cos (Y/(2*R))/
      Real.sqrt (1+(J/(9*(p : ℝ)*Real.cos (Y/(2*R))))^2))) :
    1 ≤ |localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ)-
      localDistanceModel R θ b₁ b₂ ε (rulerArc p k B j ε)| := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hSlope : 0 ≤ Real.cos (Y/(2*R))/
      Real.sqrt (1+(J/(9*(p : ℝ)*Real.cos (Y/(2*R))))^2) := by positivity
  have hsep := scaled_primeRulerGap_separated p m k δ ε A B i j
    hp hδ hε hδp hεp hsize hA hB hi hj hne
  change 3 ≤ |rulerArc p k A i δ-rulerArc p k B j ε| at hsep
  have hord : ∀ (A B i j δ ε : ℕ), 0 < δ → 0 < ε → i+δ < k → j+ε < k →
      rulerArc p k A i δ ≤ rulerArc p k B j ε →
      3 ≤ rulerArc p k B j ε-rulerArc p k A i δ →
      1 ≤ localDistanceModel R θ b₁ b₂ ε (rulerArc p k B j ε)-
        localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ) := by
    intro A B i j δ ε hd he hi hj hxy hgap
    have hδε := rulerArc_order_forces_lag_order p k A B i j δ ε hp.pos hxy
    have he' : (ε : ℝ) ≤ k := by exact_mod_cast (show ε ≤ k by omega)
    have hfeat : θ*(ε : ℝ) ≤ Real.pi/2 :=
      (mul_le_mul_of_nonneg_left he' hθ).trans hfeature
    have h := localDistanceModel_lower_gap R Y θ b₁ b₂ δ ε
      (rulerArc p k A i δ) (rulerArc p k B j ε) J (9*(p : ℝ))
      hR hangle hγ hθ (by exact_mod_cast hd) (by exact_mod_cast hδε) hfeat
      (by positivity) (rulerArc_lower p k A i δ hp.pos hd)
      (rulerArc_lower p k B j ε hp.pos he) hxy
      ((rulerArc_upper p k B j ε hp.pos hj).trans hY) hJ hJbound
    have hm := mul_le_mul_of_nonneg_left hgap hSlope
    nlinarith
  rcases le_total (rulerArc p k A i δ) (rulerArc p k B j ε) with hxy | hyx
  · have hg : 3 ≤ rulerArc p k B j ε-rulerArc p k A i δ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hsep
      linarith
    have h := hord A B i j δ ε hδ hε hi hj hxy hg
    have hab := le_abs_self (localDistanceModel R θ b₁ b₂ ε (rulerArc p k B j ε)-
      localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ))
    rw [abs_sub_comm] at hab
    exact h.trans hab
  · have hg : 3 ≤ rulerArc p k A i δ-rulerArc p k B j ε := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hsep
      exact hsep
    exact (hord B A j i ε δ hε hδ hj hi hyx hg).trans (le_abs_self _)

/-- The minimum local distance is checked separately; pairwise gaps do not imply it. -/
theorem local_ruler_model_ge_one (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ)
    (hi : i+δ < k) (R Y θ b₁ b₂ : ℝ) (hR : 0 < R) (hY : 12*(p : ℝ)*k ≤ Y)
    (hangle : Y/(2*R) ≤ Real.pi) (hγ : 0 ≤ Real.cos (Y/(2*R)))
    (hguard : 1 ≤ Real.cos (Y/(2*R))*(9*(p : ℝ))) :
    1 ≤ localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hδ' : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hl := rulerArc_lower p k A i δ hp hδ
  have hd : 0 ≤ rulerArc p k A i δ := by nlinarith
  have hC := circleChord_lower R Y (rulerArc p k A i δ) hR hangle hd
    ((rulerArc_upper p k A i δ hp hi).trans hY)
  have hmul := mul_le_mul_of_nonneg_left
    (show 9*(p : ℝ) ≤ rulerArc p k A i δ by nlinarith) hγ
  have hC₁ : 1 ≤ circleChord R (rulerArc p k A i δ) := by linarith
  have hsq := localDistanceModel_square R θ b₁ b₂ δ (rulerArc p k A i δ)
  have hpos := localDistanceModel_nonneg R θ b₁ b₂ δ (rulerArc p k A i δ)
  have hQ := harmonicEnergy_nonneg θ b₁ b₂ δ
  nlinarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
