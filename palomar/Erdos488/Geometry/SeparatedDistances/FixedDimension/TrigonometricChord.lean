module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-! Actual trigonometric circle identities and uniform chord lower slope.
These provide analytic inputs, not an assumed final Euclidean configuration. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def circleChord (R d : ℝ) : ℝ := 2*R*Real.sin (d/(2*R))

/-- The squared coordinate distance on a unit circle is the half-angle chord square. -/
theorem unit_circle_chord_square (x y : ℝ) :
    (Real.cos x-Real.cos y)^2+(Real.sin x-Real.sin y)^2 =
      (2*Real.sin ((x-y)/2))^2 := by
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hh := Real.sin_sq_eq_half_sub ((x-y)/2)
  have hc := Real.cos_sub x y
  rw [show 2*((x-y)/2)=x-y by ring] at hh
  nlinarith

/-- Exact coordinate identity for a radius-R private circle. -/
theorem circle_chord_coordinate_square (R x y : ℝ) (hR : R ≠ 0) :
    (R*Real.cos (x/R)-R*Real.cos (y/R))^2+
      (R*Real.sin (x/R)-R*Real.sin (y/R))^2 = (circleChord R (x-y))^2 := by
  have h := unit_circle_chord_square (x/R) (y/R)
  have he : (x/R-y/R)/2=(x-y)/(2*R) := by field_simp
  rw [he] at h
  dsimp [circleChord]
  have hm := congrArg (fun z : ℝ => R^2*z) h
  nlinarith only [hm]

/-- The derivative of the actual scaled circle chord. -/
theorem hasDerivAt_circleChord (R d : ℝ) (hR : R ≠ 0) :
    HasDerivAt (circleChord R) (Real.cos (d/(2*R))) d := by
  have h := (((hasDerivAt_id d).div_const (2*R)).sin).const_mul (2*R)
  have he : 2*R*(Real.cos (d/(2*R))*(1/(2*R)))=Real.cos (d/(2*R)) := by
    field_simp
  convert h using 1 <;> first | rfl | exact he.symm

/-- Uniform lower slope on the full ruler interval, not merely at sampled points. -/
theorem circleChord_lower_difference (R Y x y : ℝ) (hR : 0 < R)
    (hangle : Y/(2*R) ≤ Real.pi) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    Real.cos (Y/(2*R))*(y-x) ≤ circleChord R y-circleChord R x := by
  have hd (z : ℝ) := hasDerivAt_circleChord R z hR.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx, hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  rw [(hd z).deriv]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (div_nonneg hz'.1 (by positivity)) hangle
    ((div_le_div_iff_of_pos_right (by positivity)).2 hz'.2)

/-- In particular every ruler chord has a certified positive linear lower bound. -/
theorem circleChord_lower (R Y d : ℝ) (hR : 0 < R)
    (hangle : Y/(2*R) ≤ Real.pi) (hd : 0 ≤ d) (hdY : d ≤ Y) :
    Real.cos (Y/(2*R))*d ≤ circleChord R d := by
  have h := circleChord_lower_difference R Y 0 d hR hangle (by norm_num) hd hdY
  simpa [circleChord] using h

/-- A circle chord never exceeds its nonnegative arc length. -/
theorem circleChord_le_arc (R d : ℝ) (hR : 0 < R) (hd : 0 ≤ d) :
    circleChord R d ≤ d := by
  have h := Real.sin_le (show 0 ≤ d/(2*R) by positivity)
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*R by positivity)
  have he : 2*R*(d/(2*R))=d := by field_simp
  simpa [circleChord,he] using hmul

/-- Algebraic replacement for differentiating the full square-root length.
The feature energy may increase between endpoints. This is essential for
comparisons between different lag classes. -/
theorem augmented_length_lower_gap (C₀ C₁ Q₀ Q₁ D₀ D₁ K : ℝ)
    (hC₀ : 0 < C₀) (hC : C₀ ≤ C₁) (hQ : Q₀ ≤ Q₁)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hK : 0 < K)
    (hsq₀ : D₀^2=C₀^2+Q₀) (hsq₁ : D₁^2=C₁^2+Q₁)
    (hcone₀ : D₀ ≤ K*C₀) (hcone₁ : D₁ ≤ K*C₁) :
    (C₁-C₀)/K ≤ D₁-D₀ := by
  have hmono : 0 ≤ D₁-D₀ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left
    (show D₁+D₀ ≤ K*(C₁+C₀) by nlinarith) hmono
  have hsqgap : (C₁-C₀)*(C₁+C₀) ≤ (D₁-D₀)*(D₁+D₀) := by nlinarith
  have hcancel : C₁-C₀ ≤ K*(D₁-D₀) :=
    (mul_le_mul_iff_of_pos_right (show 0 < C₁+C₀ by linarith)).1 (by nlinarith [hmul])
  apply (div_le_iff₀ hK).2
  nlinarith

/-- A quadratic feature-to-chord bound gives the exact cone constant. -/
theorem augmented_length_cone (C Q D q : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsq : D^2=C^2+Q) (hQ : Q ≤ q^2*C^2) :
    D ≤ Real.sqrt (1+q^2)*C := by
  have hs : Real.sqrt (1+q^2)^2=1+q^2 := Real.sq_sqrt (by positivity)
  have hp : 0 ≤ Real.sqrt (1+q^2)*C := mul_nonneg (Real.sqrt_nonneg _) hC
  have he : (Real.sqrt (1+q^2)*C)^2=(1+q^2)*C^2 := by
    rw [mul_pow,hs]
  nlinarith [sq_nonneg (D-Real.sqrt (1+q^2)*C)]

/-- Local distance lower slope, allowing a nondecreasing harmonic feature energy.
The full square identity and both cone bounds are visible hypotheses. -/
theorem local_length_lower_difference (R Y x y Q₀ Q₁ D₀ D₁ K : ℝ)
    (hR : 0 < R) (hangle : Y/(2*R) ≤ Real.pi)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y)
    (hchord : 0 < circleChord R x) (hγ : 0 ≤ Real.cos (Y/(2*R)))
    (hQ : Q₀ ≤ Q₁) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hK : 0 < K)
    (hsq₀ : D₀^2=(circleChord R x)^2+Q₀)
    (hsq₁ : D₁^2=(circleChord R y)^2+Q₁)
    (hcone₀ : D₀ ≤ K*circleChord R x) (hcone₁ : D₁ ≤ K*circleChord R y) :
    (Real.cos (Y/(2*R))/K)*(y-x) ≤ D₁-D₀ := by
  have hch := circleChord_lower_difference R Y x y hR hangle hx hxy hy
  have hmon : circleChord R x ≤ circleChord R y := by
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr hxy)]
  have h := augmented_length_lower_gap (circleChord R x) (circleChord R y)
    Q₀ Q₁ D₀ D₁ K hchord hmon hQ hD₀ hD₁ hK hsq₀ hsq₁ hcone₀ hcone₁
  have hd := div_le_div_of_nonneg_right hch hK.le
  have he : Real.cos (Y/(2*R))*(y-x)/K=(Real.cos (Y/(2*R))/K)*(y-x) := by ring
  rw [he] at hd
  exact hd.trans h

end Erdos488.Geometry.SeparatedDistances.FixedDimension
