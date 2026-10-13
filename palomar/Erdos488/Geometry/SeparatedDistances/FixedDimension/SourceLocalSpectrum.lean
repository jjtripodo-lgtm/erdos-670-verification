module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceLocalGuards

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sourceRadius (m k : ℕ) : ℝ := Real.sqrt 17500*(m : ℝ)*(k : ℝ)^2
noncomputable def sourceTheta (k : ℕ) : ℝ := Real.sqrt (1/32)/(k : ℝ)
noncomputable def sourceLocalDistance (p m k : ℕ) (b₁ b₂ : ℝ) (A i δ : ℕ) : ℝ :=
  localDistanceModel (sourceRadius m k) (sourceTheta k) b₁ b₂ δ (rulerArc p k A i δ)

theorem sourceRadius_square (m k : ℕ) :
    (sourceRadius m k)^2=17500*(m : ℝ)^2*(k : ℝ)^4 := by
  unfold sourceRadius
  rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num)]
  ring

theorem sourceRadius_pos (m k : ℕ) (hm : 0 < m) (hk : 0 < k) : 0 < sourceRadius m k := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold sourceRadius
  positivity

theorem sourceTheta_pos (k : ℕ) (hk : 0 < k) : 0 < sourceTheta k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold sourceTheta
  positivity

theorem sourceTheta_feature_angle (k : ℕ) (hk : 0 < k) : sourceTheta k*(k : ℝ) ≤ Real.pi/2 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have he : sourceTheta k*(k : ℝ)=Real.sqrt (1/32) := by unfold sourceTheta; field_simp
  rw [he]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1/32 by norm_num)
  have hn := Real.sqrt_nonneg (1/32 : ℝ)
  have hp := Real.two_le_pi
  nlinarith

/-- All source local distances are separated, uniformly in m,k, once the
whole-operator harmonic budget is supplied. Radius, sine, arc and slope guards
are discharged internally, rather than exposed as conclusion-sized premises. -/
theorem source_local_spectrum_separated (p m k A B i j δ ε : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hp : p.Prime)
    (hsize : 2*m*k < p) (hupper : p < 4*m*k)
    (hA : A < m) (hB : B < m) (hδ : 0 < δ) (hε : 0 < ε)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬(A=B ∧ i=j ∧ δ=ε))
    (b₁ b₂ : ℝ)
    (hbudget : (sourceTheta k)^2*(b₁^2+4*b₂^2) ≤ 600*(m : ℝ)^2*(k : ℝ)^2) :
    1 ≤ |sourceLocalDistance p m k b₁ b₂ A i δ-sourceLocalDistance p m k b₁ b₂ B j ε| := by
  let R := sourceRadius m k
  let Y : ℝ := 48*(m : ℝ)*(k : ℝ)^2
  let J := Real.sqrt ((sourceTheta k)^2*(b₁^2+4*b₂^2))
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR : 0 < R := sourceRadius_pos m k (by omega) (by omega)
  have hRsq : R^2=17500*(m : ℝ)^2*(k : ℝ)^4 := sourceRadius_square m k
  have hpLower : 2*(m : ℝ)*(k : ℝ) ≤ p := by exact_mod_cast hsize.le
  have hpUpper : (p : ℝ) ≤ 4*(m : ℝ)*(k : ℝ) := by exact_mod_cast hupper.le
  have hY : 12*(p : ℝ)*k ≤ Y := by
    have h := mul_le_mul_of_nonneg_right hpUpper (show 0 ≤ 12*(k : ℝ) by positivity)
    dsimp [Y]
    nlinarith
  have hangle : Y/(2*R) ≤ Real.pi := by
    have h := source_local_angle_bound m k R hm₀ hk₀ hR hRsq
    dsimp [Y]
    linarith [Real.two_le_pi]
  have hγ : 0 < Real.cos (Y/(2*R)) := by
    have h := source_local_cosine_lower m k R hm₀ hk₀ hR hRsq
    dsimp [Y]
    linarith
  have hJsq : J^2=(sourceTheta k)^2*(b₁^2+4*b₂^2) := Real.sq_sqrt (by positivity)
  have hJbudget : J^2 ≤ 600*(m : ℝ)^2*(k : ℝ)^2 := hJsq ▸ hbudget
  have hkp : k < p := by
    have hh : k ≤ 2*m*k := by
      have hm₁ : 1 ≤ 2*m := by omega
      simpa using Nat.mul_le_mul_right k hm₁
    exact lt_of_le_of_lt hh hsize
  exact local_ruler_model_separated p m k A B i j δ ε hp hδ hε
    (lt_trans (by omega) hkp) (lt_trans (by omega) hkp) hsize hA hB hi hj hne
    R Y (sourceTheta k) b₁ b₂ J hR hY hangle hγ
    (sourceTheta_pos k (by omega)).le (sourceTheta_feature_angle k (by omega))
    (Real.sqrt_nonneg _) hJsq.ge
    (source_local_slope_guard m k p R J hm₀ hk₀ hpLower hR hRsq hJbudget)

/-- Zero is handled independently for the source's actual radius and prime bounds. -/
theorem source_local_distance_ge_one (p m k A i δ : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hp : 0 < p)
    (hsize : 2*m*k < p) (hupper : p < 4*m*k) (hδ : 0 < δ) (hi : i+δ < k)
    (b₁ b₂ : ℝ) : 1 ≤ sourceLocalDistance p m k b₁ b₂ A i δ := by
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR := sourceRadius_pos m k (by omega) (by omega)
  have hRsq := sourceRadius_square m k
  have hpLower : 2*(m : ℝ)*(k : ℝ) ≤ p := by exact_mod_cast hsize.le
  have hpUpper : (p : ℝ) ≤ 4*(m : ℝ)*(k : ℝ) := by exact_mod_cast hupper.le
  have hY : 12*(p : ℝ)*k ≤ 48*(m : ℝ)*(k : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_right hpUpper (show 0 ≤ 12*(k : ℝ) by positivity)
    nlinarith
  have hangle := source_local_angle_bound m k (sourceRadius m k) hm₀ hk₀ hR hRsq
  have hγ := source_local_cosine_lower m k (sourceRadius m k) hm₀ hk₀ hR hRsq
  exact local_ruler_model_ge_one p k A i δ hp hδ hi (sourceRadius m k)
    (48*(m : ℝ)*(k : ℝ)^2) (sourceTheta k) b₁ b₂ hR hY
    (by linarith [Real.two_le_pi]) (by linarith)
    (source_local_zero_guard m k p (sourceRadius m k)
      (by exact_mod_cast (show 1 ≤ m by omega)) (by exact_mod_cast hk) hpLower hR hRsq)

end Erdos488.Geometry.SeparatedDistances.FixedDimension
