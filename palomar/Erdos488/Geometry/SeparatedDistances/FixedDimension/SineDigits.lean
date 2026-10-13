module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.TrigonometricChord

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sineDigit (θ center x : ℝ) : ℝ := Real.sin (θ*(x-center))/θ

theorem hasDerivAt_sineDigit (θ center x : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (sineDigit θ center) (Real.cos (θ*(x-center))) x := by
  have h := ((((hasDerivAt_id x).sub_const center).const_mul θ).sin).div_const θ
  have he : (Real.cos (θ*(x-center))*(θ*1))/θ=Real.cos (θ*(x-center)) := by field_simp
  convert h using 1 <;> first | rfl | exact he.symm

/-- The normalized sine digit never exceeds its centered coordinate in magnitude. -/
theorem sineDigit_abs_le (θ center x : ℝ) (hθ : 0 < θ) :
    |sineDigit θ center x| ≤ |x-center| := by
  unfold sineDigit
  rw [abs_div,abs_of_pos hθ]
  calc
    |Real.sin (θ*(x-center))|/θ ≤ |θ*(x-center)|/θ :=
      div_le_div_of_nonneg_right Real.abs_sin_le_abs hθ.le
    _ = |x-center| := by rw [abs_mul,abs_of_pos hθ]; field_simp

/-- Centered coordinate bounds apply to every digit in the full interval. -/
theorem sineDigit_centered_bound (θ center x : ℝ) (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxc : x ≤ 2*center) : |sineDigit θ center x| ≤ center := by
  apply (sineDigit_abs_le θ center x hθ).trans
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Uniform adjacent and nonadjacent sine digit lower slope on the centered interval. -/
theorem sineDigit_lower_difference (θ center x y : ℝ) (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*center) :
    (1-(θ*center)^2/2)*(y-x) ≤ sineDigit θ center y-sineDigit θ center x := by
  have hc : 0 ≤ center := by linarith
  have hd (z : ℝ) := hasDerivAt_sineDigit θ center z hθ.ne'
  apply (convex_Icc (0 : ℝ) (2*center)).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) (2*center) := interior_subset hz
  have hb : |z-center| ≤ center := abs_le.mpr ⟨by linarith [hz'.1],by linarith [hz'.2]⟩
  have harg : |θ*(z-center)| ≤ |θ*center| := by
    rw [abs_mul,abs_mul,abs_of_pos hθ,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hb hθ.le
  have hsq : (θ*(z-center))^2 ≤ (θ*center)^2 := sq_le_sq.mpr harg
  rw [(hd z).deriv]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ*(z-center))
  linarith

/-- Source-shaped finite digit bound, valid for all k and every legal index. -/
theorem finite_sineDigit_bound (θ : ℝ) (k i : ℕ) (hθ : 0 < θ) (hi : i < k) :
    |sineDigit θ (((k : ℝ)-1)/2) i| ≤ ((k : ℝ)-1)/2 := by
  apply sineDigit_centered_bound θ (((k : ℝ)-1)/2) i hθ (by positivity)
  have h : (i : ℝ)+1 ≤ k := by exact_mod_cast hi
  linarith

/-- Uniform lower step from the source's θ²k²≤epsilon envelope. -/
theorem finite_sineDigit_step (θ ε : ℝ) (k i : ℕ) (hθ : 0 < θ)
    (hi : i+1 < k) (hscale : θ^2*(k : ℝ)^2 ≤ ε) :
    1-ε/8 ≤ sineDigit θ (((k : ℝ)-1)/2) (i+1)-
      sineDigit θ (((k : ℝ)-1)/2) i := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hi' : (i : ℝ)+2 ≤ k := by exact_mod_cast hi
  have h := sineDigit_lower_difference θ (((k : ℝ)-1)/2) i ((i : ℝ)+1)
    hθ (by positivity) (by linarith) (by linarith)
  have hb : θ^2*((k : ℝ)-1)^2 ≤ θ^2*(k : ℝ)^2 := by
    have hsq : ((k : ℝ)-1)^2 ≤ (k : ℝ)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg θ)
  norm_num at h
  nlinarith

/-- The fixed epsilon1/32 source gives r=255/256 uniformly. -/
theorem finite_sineDigit_source_step (θ : ℝ) (k i : ℕ) (hθ : 0 < θ)
    (hi : i+1 < k) (hscale : θ^2*(k : ℝ)^2 ≤ 1/32) :
    (255 : ℝ)/256 ≤ sineDigit θ (((k : ℝ)-1)/2) (i+1)-
      sineDigit θ (((k : ℝ)-1)/2) i := by
  have h := finite_sineDigit_step θ (1/32) k i hθ hi hscale
  norm_num at h ⊢
  exact h

/-- The source square-root scaling meets the required uniform envelope exactly. -/
theorem source_theta_scale (k : ℕ) (hk : 0 < k) :
    (Real.sqrt (1/32)/(k : ℝ))^2*(k : ℝ)^2=1/32 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [div_pow,Real.sq_sqrt (by norm_num)]
  field_simp

end Erdos488.Geometry.SeparatedDistances.FixedDimension
