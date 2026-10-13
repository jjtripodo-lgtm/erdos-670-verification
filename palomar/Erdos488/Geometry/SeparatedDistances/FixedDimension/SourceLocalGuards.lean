module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceCrossSpectrum
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.LocalRulerSeparation

@[expose] public section

/-! Coarse rational guards sufficient for all source local distances.
The budget600 deliberately leaves slack above the source's J² envelope. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The literal radius makes the universal ruler half-angle at most one quarter. -/
theorem source_local_angle_bound (m k R : ℝ) (hm : 0 < m) (hk : 0 < k) (hR : 0 < R)
    (hRsq : R^2=17500*m^2*k^4) : (48*m*k^2)/(2*R) ≤ 1/4 := by
  have ht : 0 < m*k^2 := mul_pos hm (sq_pos_of_pos hk)
  have he : R^2=17500*(m*k^2)^2 := by nlinarith only [hRsq]
  have hl : 96*(m*k^2) ≤ R := by nlinarith
  apply (div_le_iff₀ (show 0 < 2*R by positivity)).2
  nlinarith

/-- A conservative 9/10 lower cosine bound follows uniformly, with no sample grid. -/
theorem source_local_cosine_lower (m k R : ℝ) (hm : 0 < m) (hk : 0 < k) (hR : 0 < R)
    (hRsq : R^2=17500*m^2*k^4) :
    (9/10 : ℝ) ≤ Real.cos ((48*m*k^2)/(2*R)) := by
  have h₀ : 0 ≤ (48*m*k^2)/(2*R) := by positivity
  have h₁ := source_local_angle_bound m k R hm hk hR hRsq
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (48*m*k^2)/(2*R))
  have hs : ((48*m*k^2)/(2*R))^2 ≤ (1/4 : ℝ)^2 := by nlinarith
  nlinarith

/-- One abstract local-slope guard, with a deliberately slack universal budget. -/
theorem local_slope_guard_of_coarse_budget (u p γ J : ℝ)
    (hu : 0 < u) (hp : 2*u ≤ p) (hγ : 9/10 ≤ γ) (hJ : J^2 ≤ 600*u^2) :
    1 ≤ 3*(γ/Real.sqrt (1+(J/(9*p*γ))^2)) := by
  have hp₀ : 0 < p := by linarith
  have hγ₀ : 0 < γ := by linarith
  have hd : 0 < 9*p*γ := by positivity
  have hg := mul_le_mul_of_nonneg_left hγ (show 0 ≤ 9*p by positivity)
  have hden : 15*u ≤ 9*p*γ := by nlinarith
  have hs := (sq_le_sq₀ (show 0 ≤ 15*u by positivity) hd.le).2 hden
  have hq : (J/(9*p*γ))^2 ≤ 3 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    nlinarith
  have hsqrt : Real.sqrt (1+(J/(9*p*γ))^2) ≤ 2 := by
    have h := Real.sqrt_le_sqrt (show 1+(J/(9*p*γ))^2 ≤ 4 by linarith)
    norm_num at h
    exact h
  have hsqrtpos : 0 < Real.sqrt (1+(J/(9*p*γ))^2) := Real.sqrt_pos.2 (by positivity)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hsqrtpos).2
  nlinarith

/-- Uniform source local slope certificate in the original m,k,p,R,J variables. -/
theorem source_local_slope_guard (m k p R J : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hp : 2*m*k ≤ p) (hR : 0 < R)
    (hRsq : R^2=17500*m^2*k^4) (hJ : J^2 ≤ 600*m^2*k^2) :
    1 ≤ 3*(Real.cos ((48*m*k^2)/(2*R))/
      Real.sqrt (1+(J/(9*p*Real.cos ((48*m*k^2)/(2*R))))^2)) := by
  apply local_slope_guard_of_coarse_budget (m*k) p _ J (mul_pos hm hk)
    (by nlinarith) (source_local_cosine_lower m k R hm hk hR hRsq)
  nlinarith only [hJ]

/-- The first positive local distance clears zero by a separate uniform estimate. -/
theorem source_local_zero_guard (m k p R : ℝ) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hp : 2*m*k ≤ p) (hR : 0 < R) (hRsq : R^2=17500*m^2*k^4) :
    1 ≤ Real.cos ((48*m*k^2)/(2*R))*(9*p) := by
  have hm₀ : 0 < m := by linarith
  have hk₀ : 0 < k := by linarith
  have hcos := source_local_cosine_lower m k R hm₀ hk₀ hR hRsq
  have hmk : 2 ≤ m*k := by nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hk)]
  have hp₀ : 0 < p := by nlinarith
  have h := mul_le_mul_of_nonneg_right hcos (show 0 ≤ 9*p by positivity)
  nlinarith

/-- The documented exact source operator envelope is strictly below the slack budget600. -/
theorem source_J_budget_below_six_hundred :
    (20175033783589348897071 : ℝ)/38009099183104000000 < 600 := by norm_num

end Erdos488.Geometry.SeparatedDistances.FixedDimension
