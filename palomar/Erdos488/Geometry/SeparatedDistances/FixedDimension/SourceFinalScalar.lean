module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceReserveBudgets
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.AllNArithmetic

@[expose] public section

/-! Scalar diameter estimates for the literal fixed-dimensional source construction. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The full source diameter cap is below `0.735 (mk)^2`, uniformly in the
number of macro clusters and the cluster size. -/
theorem source_diameter_cap_lt (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    sourceMacroStep (k : ℝ) *
        ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
      sourcePerturbationBound (k : ℝ) +
      sourceError (sourceOffset m : ℝ) (k : ℝ) <
        (147 / 200 : ℝ) * ((m : ℝ) * (k : ℝ)) ^ 2 := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (sourceOffset m : ℝ) ≤ (m : ℝ) ^ 2 / 63 := by
    have h := sourceOffset_plus_m_upper m hm
    linarith
  have hM : (m.choose 2 : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hS : 0 ≤ sourceMacroStep (k : ℝ) := by
    unfold sourceMacroStep
    positivity
  have hmain := mul_le_mul_of_nonneg_left (add_le_add hK hM) hS
  have hA := source_perturbation_quadratic_bound (k : ℝ) hk'
  have hE := source_error_linear_bound (sourceOffset m : ℝ) (k : ℝ)
    (sourceOffset_lower m hm) hk'
  have hksq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hAE : sourcePerturbationBound (k : ℝ) +
      sourceError (sourceOffset m : ℝ) (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    nlinarith
  have hmsq : (34000 : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith
  have hmk := mul_le_mul_of_nonneg_right hmsq (sq_nonneg (k : ℝ))
  unfold sourceMacroStep at hmain
  unfold sourceMacroStep
  nlinarith

/-- Rounding from the source size `mk` to any requested `n` leaves enough
room below the target coefficient `37/50`. -/
theorem source_rounded_diameter_lt (n m k : ℕ) (hn : 68000 ≤ n)
    (hm : 34000 ≤ m) (hk : 2 ≤ k)
    (hsurplus : m * k < n + k)
    (hkbound : 34000 * k ≤ n) :
    sourceMacroStep (k : ℝ) *
        ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
      sourcePerturbationBound (k : ℝ) +
      sourceError (sourceOffset m : ℝ) (k : ℝ) <
        (37 / 50 : ℝ) * (n : ℝ) ^ 2 := by
  have hcap := source_diameter_cap_lt m k hm hk
  have hn' : (68000 : ℝ) ≤ n := by exact_mod_cast hn
  have hsize' : (m : ℝ) * (k : ℝ) < (n : ℝ) + (k : ℝ) := by
    exact_mod_cast hsurplus
  have hkbound' : (34000 : ℝ) * (k : ℝ) ≤ n := by
    exact_mod_cast hkbound
  have hratio : (m : ℝ) * (k : ℝ) < (34001 / 34000 : ℝ) * n := by
    nlinarith
  have hnonneg : 0 ≤ (m : ℝ) * (k : ℝ) := by positivity
  have hrnonneg : 0 ≤ (34001 / 34000 : ℝ) * n := by positivity
  have hsquare : ((m : ℝ) * (k : ℝ)) ^ 2 <
      ((34001 / 34000 : ℝ) * n) ^ 2 := by nlinarith
  have htarget : (147 / 200 : ℝ) *
      ((34001 / 34000 : ℝ) * n) ^ 2 < (37 / 50 : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < n by linarith)]
  nlinarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
