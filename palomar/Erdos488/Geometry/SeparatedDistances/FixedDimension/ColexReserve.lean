module

public import Erdos488.Geometry.SeparatedDistances.ColexPositivity

@[expose] public section

/-! Stronger-offset colex remainder control for the fixed-dimensional candidate.
The predecessor theorem's exact source is blob
8d62b42bc6da2281fbc54ba4659b7a9265964b76 in john-lean-math. -/

namespace Erdos488.Geometry.SeparatedDistances
open scoped BigOperators
open Matrix

theorem colex_remainder_abs_le_fiftyfive_oneTwentyEight_Q {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m + 1) : ℝ) ^ 2 ≤ K) (x : Fin m → ℝ) :
    |star x ⬝ᵥ (colexRemainder K *ᵥ x)| ≤ (55 / 128 : ℝ) * colexQ K x := by
  let H : ℝ := (harmonic (m + 1) : ℝ)
  let A : ℝ := ∑ i, |x i|
  let C : ℝ := ∑ i, (i.val + 1 : ℝ) * |x i|
  let Q : ℝ := colexQ K x
  have hH : 1 ≤ H := one_le_harmonic_of_one_le (by omega)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hKpos : 0 < K := by linarith
  have hQ : 0 ≤ Q := colexQ_nonneg hK x
  have hS0 : colexS0 (m := m) K ≤ 29 * H / K := by
    simpa [H] using (colex_S0_le (m := m) hK)
  have hS2 : colexS2 (m := m) K ≤ 26 * H := by
    simpa [H] using (colex_S2_le (m := m) hK)
  have hS0nonneg : 0 ≤ colexS0 (m := m) K := by
    unfold colexS0
    apply Finset.sum_nonneg
    intro i hi
    exact inv_nonneg.mpr (colexWeight_pos hK _ (by omega)).le
  have hcoef0 : 128 * H * colexS0 (m := m) K ≤ (29 / 128 : ℝ) := by
    have hS0K : colexS0 (m := m) K * K ≤ 29 * H := by
      apply (le_div_iff₀ hKpos).mp at hS0
      nlinarith
    have hscale := mul_le_mul_of_nonneg_left hlarge hS0nonneg
    nlinarith
  have hcoef2 : colexS2 (m := m) K / (128 * H) ≤ (26 / 128 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hHpos)).2
    nlinarith
  have hA2 : A ^ 2 ≤ colexS0 (m := m) K * Q := by
    simpa [A, Q] using colex_abs_sum_sq_le hK x
  have hC2 : C ^ 2 ≤ colexS2 (m := m) K * Q := by
    simpa [C, Q] using colex_indexed_abs_sum_sq_le hK x
  have hYoung := two_mul_le_weighted_sq (A := A) (C := C) (lambda := 128 * H)
    (mul_pos (by norm_num) hHpos)
  have hAQ : 128 * H * A ^ 2 ≤ (29 / 128 : ℝ) * Q := by
    calc
      128 * H * A ^ 2 ≤ 128 * H * (colexS0 (m := m) K * Q) := by
        exact mul_le_mul_of_nonneg_left hA2 (mul_nonneg (by norm_num) hHpos.le)
      _ = (128 * H * colexS0 (m := m) K) * Q := by ring
      _ ≤ (29 / 128 : ℝ) * Q := mul_le_mul_of_nonneg_right hcoef0 hQ
  have hCQ : C ^ 2 / (128 * H) ≤ (26 / 128 : ℝ) * Q := by
    calc
      C ^ 2 / (128 * H) ≤ (colexS2 (m := m) K * Q) / (128 * H) := by
        exact div_le_div_of_nonneg_right hC2 (mul_nonneg (by norm_num) hHpos.le)
      _ = (colexS2 (m := m) K / (128 * H)) * Q := by ring
      _ ≤ (26 / 128 : ℝ) * Q := mul_le_mul_of_nonneg_right hcoef2 hQ
  calc
    |star x ⬝ᵥ (colexRemainder K *ᵥ x)| ≤ 2 * A * C := by
      simpa [A, C] using colex_remainder_quadratic_abs_le_product K x
    _ ≤ 128 * H * A ^ 2 + C ^ 2 / (128 * H) := hYoung
    _ ≤ (29 / 128 : ℝ) * Q + (26 / 128 : ℝ) * Q := add_le_add hAQ hCQ
    _ = (55 / 128 : ℝ) * colexQ K x := by simp [Q]; ring



/-- At the candidate's larger harmonic offset the literal colex Gram retains
more than half the complete tridiagonal form, including its gradient energy. -/
theorem colex_incrementGram_ge_half_tridiagonal {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+1) : ℝ)^2 ≤ K) (x : Fin m → ℝ) :
    (1/2 : ℝ) * (star x ⬝ᵥ (colexTridiagonal K *ᵥ x)) ≤
      star x ⬝ᵥ (incrementGram (colexSqData (m := m) K) *ᵥ x) := by
  have hQ := colexQ_nonneg hK x
  have hT := colex_tridiagonal_ge_Q hm hK x
  have hR := colex_remainder_abs_le_fiftyfive_oneTwentyEight_Q hm hK hlarge x
  have hRle := le_trans (le_abs_self (star x ⬝ᵥ (colexRemainder K *ᵥ x))) hR
  rw [colex_incrementGram_eq_tridiagonal_sub_remainder]
  simp only [Matrix.sub_mulVec, dotProduct_sub]
  linarith


/-- Every path coefficient retains a quarter of its prescribed adjacent length. -/
lemma colexPathCoeff_ge_quarter {K : ℝ} (hK : 10 ≤ K) (j : ℕ) :
    colexANat K j ^ 2 / 4 ≤ colexPathCoeff K j := by
  have hc : (0 : ℝ) ≤ Nat.choose (j+1+1) 2 := by positivity
  unfold colexPathCoeff colexANat
  nlinarith [sq_nonneg (K + (Nat.choose (j+1) 2 : ℝ))]

lemma colex_first_two_weighted_path {K : ℝ} (hK : 10 ≤ K) (a b : ℝ) :
    colexANat K 1 ^ 2 / 4 * (a^2 + (a-b)^2) ≤
      colexPathCoeff K 1 * (a-b)^2 +
      colexPotential K 1 * a^2 + colexPotential K 2 * b^2 := by
  have hv : colexANat K 1 ^ 2 / 4 + 8 ≤ colexPotential K 1 := by
    norm_num [colexANat, colexPotential, Nat.choose]
    nlinarith [sq_nonneg (K-10)]
  have hc : colexANat K 1 ^ 2 / 4 + 8 ≤ colexPathCoeff K 1 := by
    norm_num [colexANat, colexPathCoeff, Nat.choose]
    nlinarith [sq_nonneg (K-10)]
  have hv' := mul_le_mul_of_nonneg_right hv (sq_nonneg a)
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (a-b))
  norm_num [colexPotential] at *
  nlinarith [sq_nonneg (2*a-b)]

/-- Weighted incidence-path domination, preserving the gradient terms discarded
by the old isotropic colex corollary. There are m increments and m+1 vertices. -/
theorem colex_tridiagonal_ge_quarter_weighted_path {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K) (x : Fin m → ℝ) :
    colexANat K 1 ^ 2 / 4 * x ⟨0, by omega⟩ ^ 2 +
      (∑ i : Fin (m-1), colexANat K (i.val+1) ^ 2 / 4 *
        (x ⟨i.val, by omega⟩ - x ⟨i.val+1, by omega⟩)^2) +
      colexANat K m ^ 2 / 4 * x ⟨m-1, by omega⟩^2 ≤
      star x ⬝ᵥ (colexTridiagonal K *ᵥ x) := by
  let z0 : Fin m := ⟨0, by omega⟩
  let z1 : Fin m := ⟨1, by omega⟩
  let e0 : Fin (m-1) := ⟨0, by omega⟩
  have hfirst := colex_first_two_weighted_path hK (x z0) (x z1)
  have htail :
      (∑ i ∈ (Finset.univ.erase e0), colexANat K (i.val+1)^2 / 4 *
        (x ⟨i.val, by omega⟩ - x ⟨i.val+1, by omega⟩)^2) ≤
      ∑ i ∈ (Finset.univ.erase e0), colexPathCoeff K (i.val+1) *
        (x ⟨i.val, by omega⟩ - x ⟨i.val+1, by omega⟩)^2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (colexPathCoeff_ge_quarter hK _) (sq_nonneg _)
  have hpotTail : 0 ≤ ∑ i ∈ (Finset.univ.erase z0).erase z1,
      colexPotential K (i.val+1) * x i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    have hi1 := Finset.mem_erase.mp hi
    have hi0 := Finset.mem_erase.mp hi1.2
    have hne1 : i ≠ z1 := hi1.1
    have hne0 : i ≠ z0 := hi0.1
    have hj : 3 ≤ i.val+1 := by
      simp [z0, z1, Fin.ext_iff] at hne0 hne1
      omega
    have hp := colexPotential_ge_weight hK hj
    have hw := colexWeight_pos hK (i.val+1) (by omega)
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hend := mul_le_mul_of_nonneg_right (colexPathCoeff_ge_quarter hK m)
    (sq_nonneg (x ⟨m-1, by omega⟩))
  rw [colex_tridiagonal_quadratic_eq hm]
  have hpath := Finset.sum_erase_add (Finset.univ : Finset (Fin (m-1)))
    (fun i => colexPathCoeff K (i.val+1) *
      (x ⟨i.val, by omega⟩ - x ⟨i.val+1, by omega⟩)^2) (Finset.mem_univ e0)
  have hweight := Finset.sum_erase_add (Finset.univ : Finset (Fin (m-1)))
    (fun i => colexANat K (i.val+1)^2 / 4 *
      (x ⟨i.val, by omega⟩ - x ⟨i.val+1, by omega⟩)^2) (Finset.mem_univ e0)
  have hp0 := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
    (fun i => colexPotential K (i.val+1) * x i ^ 2) (Finset.mem_univ z0)
  have hp1 := Finset.sum_erase_add ((Finset.univ : Finset (Fin m)).erase z0)
    (fun i => colexPotential K (i.val+1) * x i ^ 2) (a := z1) (by
      apply Finset.mem_erase.mpr
      exact ⟨by simp [z0, z1, Fin.ext_iff], Finset.mem_univ _⟩)
  rw [← hpath, ← hweight, ← hp0, ← hp1]
  dsimp [e0, z0, z1] at hfirst htail hpotTail hend ⊢
  nlinarith


lemma colexANat_le_K_add_sq {K : ℝ} (j : ℕ) :
    colexANat K j ≤ K + (j:ℝ)^2 := by
  unfold colexANat
  push_cast [Nat.cast_choose_two]
  have hj : (0:ℝ) ≤ j := by positivity
  have hprod : (j:ℝ) ≤ (j:ℝ)^2 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · norm_num
    · have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj'
      nlinarith
  nlinarith

/-- Complementary diagonal weight bound. This uses the existing comparison
form, independently of the new gradient-energy inequality. -/
lemma colexWeight_ge_adjacent_square {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m)
    {K : ℝ} (hK : 10 ≤ K) :
    colexANat K j ^ 2 ≤ 36*(K+m)*colexWeight K j := by
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hj0 : (0:ℝ) ≤ j := by positivity
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hjmR : (j:ℝ) ≤ m := by exact_mod_cast hjm
  have hp0 : 0 ≤ colexANat K j := by unfold colexANat; positivity
  have hp := colexANat_le_K_add_sq (K:=K) j
  unfold colexWeight
  split_ifs with hj2
  · have hcases : j=1 ∨ j=2 := by omega
    rcases hcases with rfl | rfl <;> norm_num [colexANat, Nat.choose] <;>
      nlinarith [sq_nonneg (K-10), mul_nonneg hm0 (sq_nonneg K)]
  · have h₁ : K+(j:ℝ)^2 ≤ (K+m)*j := by
      have ht := mul_nonneg (sub_nonneg.mpr hj1) (show 0 ≤ K by linarith)
      have hu := mul_nonneg (sub_nonneg.mpr hjmR) hj0
      nlinarith
    have h₂ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ K+(j:ℝ)^2 by positivity)
    have h₃ : colexANat K j ^ 2 ≤ (K+(j:ℝ)^2)^2 := by nlinarith
    have h₄ : 0 ≤ (K+m)*(K*j+(j:ℝ)^3) := by positivity
    nlinarith


/-- The full tridiagonal form controls the complementary adjacent-length
weighted diagonal form with the candidate's constant 36. -/
theorem colex_tridiagonal_ge_adjacent_diagonal {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K) (x : Fin m → ℝ) :
    (∑ i, colexANat K (i.val+1)^2 * x i ^ 2) ≤
      36*(K+m) * (star x ⬝ᵥ (colexTridiagonal K *ᵥ x)) := by
  have hsum : (∑ i, colexANat K (i.val+1)^2 * x i ^ 2) ≤
      36*(K+m)*colexQ K x := by
    unfold colexQ
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right
      (colexWeight_ge_adjacent_square (m:=m) (j:=i.val+1) (by omega) (by omega) hK)
      (sq_nonneg (x i))
    simpa only [mul_assoc] using h
  exact hsum.trans (mul_le_mul_of_nonneg_left (colex_tridiagonal_ge_Q hm hK x)
    (by positivity))


/-- Scalar assembly of the two reserves after an off-diagonal radius shift.
The literal incidence/weighted-path identification remains a separate bridge. -/
theorem radius_shift_preserves_two_reserves (G T W L r K : ℝ)
    (hL : 0 ≤ L) (hG : T/2 ≤ G) (hT : W/4 ≤ T)
    (hW : K^2*L ≤ W) (hr : r ≤ K^2/16) :
    W/16 ≤ G-r*L ∧ T/4 ≤ G-r*L := by
  have hcost := mul_le_mul_of_nonneg_right hr hL
  constructor <;> nlinarith

end Erdos488.Geometry.SeparatedDistances
