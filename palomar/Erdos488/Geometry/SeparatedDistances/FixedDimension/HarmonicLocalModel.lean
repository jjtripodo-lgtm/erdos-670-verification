module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.TrigonometricChord

@[expose] public section

/-! Literal two-harmonic local distance model: feature monotonicity, cone bounds,
and uniform lower separation transfer. This is independent of the global Gram construction. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def harmonicEnergy (θ b₁ b₂ δ : ℝ) : ℝ :=
  (2*b₁*Real.sin (θ*δ/2))^2+(2*b₂*Real.sin (θ*δ))^2

noncomputable def localDistanceModel (R θ b₁ b₂ δ d : ℝ) : ℝ :=
  Real.sqrt ((circleChord R d)^2+harmonicEnergy θ b₁ b₂ δ)

theorem harmonicEnergy_nonneg (θ b₁ b₂ δ : ℝ) : 0 ≤ harmonicEnergy θ b₁ b₂ δ := by
  unfold harmonicEnergy
  positivity

/-- Increasing positive lags increase both squared harmonic features. -/
theorem harmonicEnergy_mono (θ b₁ b₂ δ ε : ℝ) (hθ : 0 ≤ θ)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (hangle : θ*ε ≤ Real.pi/2) :
    harmonicEnergy θ b₁ b₂ δ ≤ harmonicEnergy θ b₁ b₂ ε := by
  have hmul : θ*δ ≤ θ*ε := mul_le_mul_of_nonneg_left hδε hθ
  have hzero : 0 ≤ θ*δ := mul_nonneg hθ hδ
  have hs₁ : Real.sin (θ*δ/2) ≤ Real.sin (θ*ε/2) :=
    Real.monotoneOn_sin ⟨by linarith [Real.pi_pos],by linarith⟩
      ⟨by linarith [Real.pi_pos],by linarith⟩ (by linarith)
  have hs₂ : Real.sin (θ*δ) ≤ Real.sin (θ*ε) :=
    Real.monotoneOn_sin ⟨by linarith [Real.pi_pos],by linarith⟩
      ⟨by linarith [Real.pi_pos],hangle⟩ hmul
  have hp₁ : 0 ≤ Real.sin (θ*δ/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hp₂ : 0 ≤ Real.sin (θ*δ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hzero (by linarith [Real.pi_pos])
  have hsq₁ := sq_le_sq₀ hp₁ (hp₁.trans hs₁) |>.2 hs₁
  have hsq₂ := sq_le_sq₀ hp₂ (hp₂.trans hs₂) |>.2 hs₂
  have hm₁ := mul_le_mul_of_nonneg_left hsq₁ (show 0 ≤ 4*b₁^2 by positivity)
  have hm₂ := mul_le_mul_of_nonneg_left hsq₂ (show 0 ≤ 4*b₂^2 by positivity)
  unfold harmonicEnergy
  nlinarith

/-- Exact global quadratic envelope for both harmonic features. -/
theorem harmonicEnergy_le_quadratic (θ b₁ b₂ δ : ℝ) :
    harmonicEnergy θ b₁ b₂ δ ≤ θ^2*(b₁^2+4*b₂^2)*δ^2 := by
  have h₁ := mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := θ*δ/2))
    (show 0 ≤ 4*b₁^2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := θ*δ))
    (show 0 ≤ 4*b₂^2 by positivity)
  unfold harmonicEnergy
  nlinarith

theorem localDistanceModel_nonneg (R θ b₁ b₂ δ d : ℝ) :
    0 ≤ localDistanceModel R θ b₁ b₂ δ d := Real.sqrt_nonneg _

theorem localDistanceModel_square (R θ b₁ b₂ δ d : ℝ) :
    (localDistanceModel R θ b₁ b₂ δ d)^2 =
      (circleChord R d)^2+harmonicEnergy θ b₁ b₂ δ := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (harmonicEnergy_nonneg _ _ _ _))

/-- A lower ruler-arc bound gives the cone ratio used by the local separation proof. -/
theorem localDistanceModel_cone (R Y θ b₁ b₂ δ d J c : ℝ)
    (hR : 0 < R) (hangle : Y/(2*R) ≤ Real.pi)
    (hγ : 0 < Real.cos (Y/(2*R))) (hδ : 0 ≤ δ) (hc : 0 < c)
    (hd : c*δ ≤ d) (hdY : d ≤ Y) (hJ : 0 ≤ J)
    (hJbound : θ^2*(b₁^2+4*b₂^2) ≤ J^2) :
    localDistanceModel R θ b₁ b₂ δ d ≤
      Real.sqrt (1+(J/(c*Real.cos (Y/(2*R))))^2)*circleChord R d := by
  have hd₀ : 0 ≤ d := le_trans (mul_nonneg hc.le hδ) hd
  have hch := circleChord_lower R Y d hR hangle hd₀ hdY
  have hC : 0 ≤ circleChord R d := le_trans (mul_nonneg hγ.le hd₀) hch
  have hbase : c*Real.cos (Y/(2*R))*δ ≤ circleChord R d := by
    have h := mul_le_mul_of_nonneg_left hd hγ.le
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hbase hJ
  have hratio : J*δ ≤ (J/(c*Real.cos (Y/(2*R))))*circleChord R d := by
    calc
      J*δ ≤ J*circleChord R d/(c*Real.cos (Y/(2*R))) :=
        (le_div_iff₀ (mul_pos hc hγ)).2 (by nlinarith)
      _ = _ := by ring
  have hQ := harmonicEnergy_le_quadratic θ b₁ b₂ δ
  have hJδ := mul_le_mul_of_nonneg_right hJbound (sq_nonneg δ)
  have hsq := sq_le_sq₀ (mul_nonneg hJ hδ)
    ((mul_nonneg hJ hδ).trans hratio) |>.2 hratio
  apply augmented_length_cone _ _ _ _ hC (localDistanceModel_nonneg _ _ _ _ _ _)
    (localDistanceModel_square _ _ _ _ _ _)
  nlinarith

/-- Uniform local-model lower gap across equal or increasing lags. -/
theorem localDistanceModel_lower_gap (R Y θ b₁ b₂ δ ε x y J c : ℝ)
    (hR : 0 < R) (hangle : Y/(2*R) ≤ Real.pi)
    (hγ : 0 < Real.cos (Y/(2*R))) (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hδε : δ ≤ ε) (hfeature : θ*ε ≤ Real.pi/2)
    (hc : 0 < c) (hx : c*δ ≤ x) (hy : c*ε ≤ y)
    (hxy : x ≤ y) (hyY : y ≤ Y) (hJ : 0 ≤ J)
    (hJbound : θ^2*(b₁^2+4*b₂^2) ≤ J^2) :
    (Real.cos (Y/(2*R))/Real.sqrt (1+(J/(c*Real.cos (Y/(2*R))))^2))*(y-x) ≤
      localDistanceModel R θ b₁ b₂ ε y-localDistanceModel R θ b₁ b₂ δ x := by
  have hx₀ : 0 < x := lt_of_lt_of_le (mul_pos hc hδ) hx
  have hch := circleChord_lower R Y x hR hangle hx₀.le (hxy.trans hyY)
  have hch₀ : 0 < circleChord R x := lt_of_lt_of_le (mul_pos hγ hx₀) hch
  exact local_length_lower_difference R Y x y
    (harmonicEnergy θ b₁ b₂ δ) (harmonicEnergy θ b₁ b₂ ε)
    (localDistanceModel R θ b₁ b₂ δ x) (localDistanceModel R θ b₁ b₂ ε y)
    (Real.sqrt (1+(J/(c*Real.cos (Y/(2*R))))^2))
    hR hangle hx₀.le hxy hyY hch₀ hγ.le
    (harmonicEnergy_mono θ b₁ b₂ δ ε hθ hδ.le hδε hfeature)
    (localDistanceModel_nonneg _ _ _ _ _ _) (localDistanceModel_nonneg _ _ _ _ _ _)
    (Real.sqrt_pos.2 (by positivity))
    (localDistanceModel_square _ _ _ _ _ _) (localDistanceModel_square _ _ _ _ _ _)
    (localDistanceModel_cone R Y θ b₁ b₂ δ x J c hR hangle hγ hδ.le hc
      hx (hxy.trans hyY) hJ hJbound)
    (localDistanceModel_cone R Y θ b₁ b₂ ε y J c hR hangle hγ (hδ.le.trans hδε) hc
      hy hyY hJ hJbound)

end Erdos488.Geometry.SeparatedDistances.FixedDimension
