module

public import Erdos488.Geometry.SeparatedDistances.ColexPositivity

@[expose] public section

/-! The direct Cauchy--Schwarz closure of the literal colex macro reserve.
This is an alternative to the weighted-Young argument in `ColexReserve`;
the matrix, comparison form, harmonic sums, and offset are unchanged. -/

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators
open Matrix

private lemma two_product_le_two_sqrt_product (a b s t q : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (ha2 : a ^ 2 ≤ s * q) (hb2 : b ^ 2 ≤ t * q) :
    2 * a * b ≤ 2 * Real.sqrt (s * t) * q := by
  have hst : 0 ≤ s * t := mul_nonneg hs ht
  have hsq : (Real.sqrt (s * t)) ^ 2 = s * t := Real.sq_sqrt hst
  have hroot : 0 ≤ Real.sqrt (s * t) := Real.sqrt_nonneg _
  have hsq1 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg b)
  have hsq2 := mul_le_mul_of_nonneg_left hb2 (mul_nonneg hs hq)
  have hprod : (a * b) ^ 2 ≤ (Real.sqrt (s * t) * q) ^ 2 := by
    calc
      (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
      _ ≤ s * q * b ^ 2 := hsq1
      _ ≤ s * q * (t * q) := hsq2
      _ = (s * t) * q ^ 2 := by ring
      _ = (Real.sqrt (s * t)) ^ 2 * q ^ 2 := by
        exact (congrArg (fun z : ℝ => z * q ^ 2) hsq).symm
      _ = (Real.sqrt (s * t) * q) ^ 2 := by ring
  nlinarith [mul_nonneg hroot hq]

private lemma sqrt_product_budget (s t H K : ℝ)
    (_hs : 0 ≤ s) (ht : 0 ≤ t) (hH : 0 ≤ H) (hK : 0 < K)
    (hlarge : 16384 * H ^ 2 ≤ K)
    (hsb : s ≤ 29 * H / K) (htb : t ≤ 26 * H) :
    2 * Real.sqrt (s * t) ≤ Real.sqrt (754 : ℝ) / 64 := by
  have hprod : s * t ≤ (754 / 16384 : ℝ) := by
    calc
      s * t ≤ (29 * H / K) * t := mul_le_mul_of_nonneg_right hsb ht
      _ ≤ (29 * H / K) * (26 * H) :=
        mul_le_mul_of_nonneg_left htb (div_nonneg (by positivity) hK.le)
      _ = 754 * H ^ 2 / K := by ring
      _ ≤ (754 / 16384 : ℝ) := by
        apply (div_le_iff₀ hK).2
        nlinarith [hlarge]
  have hsqrt := Real.sqrt_le_sqrt hprod
  have h754 : (Real.sqrt (754 : ℝ)) ^ 2 = 754 := Real.sq_sqrt (by norm_num)
  have hquot : (Real.sqrt (754 / 16384 : ℝ)) ^ 2 = 754 / 16384 :=
    Real.sq_sqrt (by norm_num)
  have hroot_eq : Real.sqrt (754 / 16384 : ℝ) = Real.sqrt (754 : ℝ) / 128 := by
    nlinarith [Real.sqrt_nonneg (754 / 16384 : ℝ), Real.sqrt_nonneg (754 : ℝ)]
  rw [hroot_eq] at hsqrt
  linarith

private lemma sqrt754_div64_lt_half : Real.sqrt (754 : ℝ) / 64 < 1 / 2 := by
  have hsq : (Real.sqrt (754 : ℝ)) ^ 2 = 754 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt (754 : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- Direct Cauchy--Schwarz on the actual colex remainder and its two
reciprocal-weight sums. The intermediate radical is retained explicitly. -/
theorem colex_remainder_abs_le_direct_cauchy {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m + 1) : ℝ) ^ 2 ≤ K) (x : Fin m → ℝ) :
    |star x ⬝ᵥ (colexRemainder K *ᵥ x)| ≤
      2 * Real.sqrt (colexS0 (m := m) K * colexS2 (m := m) K) * colexQ K x ∧
    2 * Real.sqrt (colexS0 (m := m) K * colexS2 (m := m) K) * colexQ K x ≤
      Real.sqrt (754 : ℝ) / 64 * colexQ K x := by
  let a : ℝ := ∑ i, |x i|
  let b : ℝ := ∑ i, (i.val + 1 : ℝ) * |x i|
  let q : ℝ := colexQ K x
  let H : ℝ := (harmonic (m + 1) : ℝ)
  have hq : 0 ≤ q := colexQ_nonneg hK x
  have hs : 0 ≤ colexS0 (m := m) K := by
    unfold colexS0
    apply Finset.sum_nonneg
    intro i hi
    exact inv_nonneg.mpr (colexWeight_pos hK _ (by omega)).le
  have ht : 0 ≤ colexS2 (m := m) K := by
    unfold colexS2
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (sq_nonneg _) (colexWeight_pos hK _ (by omega)).le
  have ha2 : a ^ 2 ≤ colexS0 (m := m) K * q := by
    simpa [a, q] using colex_abs_sum_sq_le hK x
  have hb2 : b ^ 2 ≤ colexS2 (m := m) K * q := by
    simpa [b, q] using colex_indexed_abs_sum_sq_le hK x
  have hH1 : 1 ≤ H := by
    simpa [H] using (one_le_harmonic_of_one_le (by omega : 1 ≤ m + 1))
  have hH : 0 ≤ H := by linarith
  have hKpos : 0 < K := by linarith
  have hsbudget : colexS0 (m := m) K ≤ 29 * H / K := by
    simpa [H] using (colex_S0_le (m := m) hK)
  have htbudget : colexS2 (m := m) K ≤ 26 * H := by
    simpa [H] using (colex_S2_le (m := m) hK)
  have hCS := two_product_le_two_sqrt_product a b
    (colexS0 (m := m) K) (colexS2 (m := m) K) q
    hs ht hq ha2 hb2
  have hcoef := sqrt_product_budget (colexS0 (m := m) K)
    (colexS2 (m := m) K) H K hs ht hH hKpos hlarge hsbudget htbudget
  constructor
  · calc
      |star x ⬝ᵥ (colexRemainder K *ᵥ x)| ≤ 2 * a * b := by
        simpa [a, b] using colex_remainder_quadratic_abs_le_product K x
      _ ≤ 2 * Real.sqrt (colexS0 (m := m) K * colexS2 (m := m) K) * q := hCS
      _ = 2 * Real.sqrt (colexS0 (m := m) K * colexS2 (m := m) K) *
          colexQ K x := rfl
  · exact mul_le_mul_of_nonneg_right hcoef hq

/-- The strict `754 < 1024` margin applies to every nonzero macro vector. -/
theorem colex_remainder_abs_lt_half_Q_direct {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m + 1) : ℝ) ^ 2 ≤ K)
    {x : Fin m → ℝ} (hx : x ≠ 0) :
    |star x ⬝ᵥ (colexRemainder K *ᵥ x)| < (1 / 2 : ℝ) * colexQ K x := by
  obtain ⟨hCS, h754⟩ := colex_remainder_abs_le_direct_cauchy hm hK hlarge x
  have hq := colexQ_pos hK hx
  exact (hCS.trans h754).trans_lt
    (mul_lt_mul_of_pos_right sqrt754_div64_lt_half hq)

/-- On the literal increment Gram, direct Cauchy--Schwarz retains half of
the actual tridiagonal quadratic form. -/
theorem colex_incrementGram_ge_half_tridiagonal_direct {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m + 1) : ℝ) ^ 2 ≤ K) (x : Fin m → ℝ) :
    (1 / 2 : ℝ) * (star x ⬝ᵥ (colexTridiagonal K *ᵥ x)) ≤
      star x ⬝ᵥ (incrementGram (colexSqData (m := m) K) *ᵥ x) := by
  have hq : 0 ≤ colexQ K x := colexQ_nonneg hK x
  have hT := colex_tridiagonal_ge_Q hm hK x
  obtain ⟨hCS, h754⟩ := colex_remainder_abs_le_direct_cauchy hm hK hlarge x
  have hcoef : Real.sqrt (754 : ℝ) / 64 ≤ 1 / 2 :=
    le_of_lt sqrt754_div64_lt_half
  have hR : star x ⬝ᵥ (colexRemainder K *ᵥ x) ≤ (1 / 2 : ℝ) * colexQ K x := by
    calc
      star x ⬝ᵥ (colexRemainder K *ᵥ x) ≤
          |star x ⬝ᵥ (colexRemainder K *ᵥ x)| := le_abs_self _
      _ ≤ Real.sqrt (754 : ℝ) / 64 * colexQ K x := hCS.trans h754
      _ ≤ (1 / 2 : ℝ) * colexQ K x := mul_le_mul_of_nonneg_right hcoef hq
  rw [colex_incrementGram_eq_tridiagonal_sub_remainder]
  simp only [Matrix.sub_mulVec, dotProduct_sub]
  linarith

end Erdos488.Geometry.SeparatedDistances
