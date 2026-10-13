module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.WeightedSchur

@[expose] public section

open scoped BigOperators Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma sqrt_recip_increment {x : ℝ} (hx : 1 ≤ x) :
    1/Real.sqrt x ≤ 2*(Real.sqrt x-Real.sqrt (x-1)) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have h₁ := Real.sq_sqrt (show 0 ≤ x by linarith)
  have h₂ := Real.sq_sqrt (show 0 ≤ x-1 by linarith)
  apply (div_le_iff₀ hs).2
  nlinarith [sq_nonneg (Real.sqrt x-Real.sqrt (x-1))]

/-- Exact telescoping row estimate for the Hardy Schur weight. -/
theorem sqrt_recip_prefix_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, 1/Real.sqrt (j+1 : ℕ)) ≤ 2*Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp := sqrt_recip_increment (x:=(n+1:ℕ)) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      norm_num only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hp ih ⊢
      linarith

lemma sqrt_recip_tail_increment {x : ℝ} (hx : 1 ≤ x) :
    1/((x+1)*Real.sqrt (x+1)) ≤
      2*(1/Real.sqrt x-1/Real.sqrt (x+1)) := by
  let u := Real.sqrt x
  let v := Real.sqrt (x+1)
  have hu : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hv : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hu2 : u^2=x := Real.sq_sqrt (by linarith)
  have hv2 : v^2=x+1 := Real.sq_sqrt (by linarith)
  have hdiff : v^2-u^2=1 := by linarith
  have hmul := congrArg (fun t : ℝ => u*t) hdiff
  have hn := mul_nonneg (sq_nonneg (v-u)) (show 0 ≤ 2*v+u by linarith)
  have hcore : u ≤ 2*(v-u)*v^2 := by nlinarith
  have hfrac : 1/(v^2*v) ≤ 2*(v-u)/(u*v) := by
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hv) hv) (mul_pos hu hv)).2
    have hm := mul_le_mul_of_nonneg_right hcore hv.le
    nlinarith
  have heq : 2*(v-u)/(u*v) = 2*(1/u-1/v) := by field_simp
  change 1/((x+1)*v) ≤ 2*(1/u-1/v)
  rw [← hv2, ← heq]
  exact hfrac

/-- Exact telescoping finite tail estimate, with the terminal correction kept. -/
theorem sqrt_recip_tail_sum (j n : ℕ) (hj : 1 ≤ j) :
    (∑ a ∈ Finset.range n,
      1/((j+a+1 : ℕ)*Real.sqrt (j+a+1 : ℕ))) ≤
      2*(1/Real.sqrt j-1/Real.sqrt (j+n : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp := sqrt_recip_tail_increment (x:=(j+n:ℕ)) (by exact_mod_cast (show 1 ≤ j+n by omega))
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] at hp ih ⊢
      linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
