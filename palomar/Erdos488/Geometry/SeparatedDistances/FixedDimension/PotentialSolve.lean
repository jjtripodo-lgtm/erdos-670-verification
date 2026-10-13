module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.IncidenceBridge

@[expose] public section

open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma weighted_duality_sq {ι : Type*} [Fintype ι]
    (P u z : ι → ℝ) (hP : ∀ i, P i ≠ 0) :
    (u ⬝ᵥ z)^2 ≤ (∑ i, P i ^ 2 * u i ^ 2) * ∑ i, (z i / P i)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => P i * u i) (fun i => z i / P i)
  have hh : ∀ i, (P i * u i) * (z i / P i) = u i * z i := by
    intro i
    field_simp [hP i]
  simpa only [hh, mul_pow, dotProduct] using h

/-- Quantitative potential solve for the actual flattened colex Gram. The
energy bound is uniform in every vertex-potential vector; no anchor, PSD or
inverse-bound hypothesis is exported. -/
theorem flattened_colex_potential_solve {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) (z : Fin (m+2) → ℝ) :
    ∃ x : Fin (m+1) → ℝ,
      incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ x =
        pathIncidence (m+1) *ᵥ z ∧
      x ⬝ᵥ (incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ x) ≤
        16 * ∑ a, (z a / macroVertexWeight K a)^2 := by
  let A := incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r)
  have hA : A.PosDef := flattened_colex_posDef hm hK hlarge r hr
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  let x := A⁻¹ *ᵥ (pathIncidence (m+1) *ᵥ z)
  have hx : A *ᵥ x = pathIncidence (m+1) *ᵥ z := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  refine ⟨x, hx, ?_⟩
  let u := (pathIncidence (m+1))ᵀ *ᵥ x
  let q := x ⬝ᵥ (A *ᵥ x)
  let C := ∑ a, (z a / macroVertexWeight K a)^2
  have hq0 : 0 ≤ q := by
    simpa only [q, star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hC : 0 ≤ C := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hP : ∀ a : Fin (m+2), macroVertexWeight K a ≠ 0 := by
    intro a
    have h := macroVertexWeight_ge_K K a
    linarith
  have hduality := weighted_duality_sq (macroVertexWeight K) u z hP
  have hqu : q = u ⬝ᵥ z := by
    dsimp [q, u]
    rw [hx, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hreserve := (flattened_colex_two_reserves hm hK hlarge r hr x).1
  have hW : (∑ a, macroVertexWeight K a ^ 2 * u a ^ 2) ≤ 16*q := by
    dsimp [u, q, A] at *
    linarith
  have hbound := mul_le_mul_of_nonneg_right hW hC
  have hsq : q*q ≤ q*(16*C) := by
    rw [← hqu] at hduality
    dsimp [C] at *
    nlinarith
  change q ≤ 16*C
  rcases eq_or_lt_of_le hq0 with hzero | hpos
  · rw [← hzero]; positivity
  · exact (mul_le_mul_iff_right₀ hpos).mp (by nlinarith [hsq])


/-- Arbitrary edge-potential energy bound. Since v may be any linear combination
of columns, this is the uniform quadratic-form input to the whole-operator
estimate, not an average or columnwise estimate. -/
theorem flattened_colex_edge_solve_energy {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) (x v : Fin (m+1) → ℝ)
    (hsolve : incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ x = v) :
    x ⬝ᵥ (incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ x) ≤
      144*(K+(m+1:ℕ)) * ∑ i, (v i / colexANat K (i.val+1))^2 := by
  let A := incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r)
  let q := x ⬝ᵥ (A *ᵥ x)
  let C := ∑ i, (v i / colexANat K (i.val+1))^2
  have hA : A.PosDef := flattened_colex_posDef hm hK hlarge r hr
  have hq0 : 0 ≤ q := by
    simpa only [q, star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hP : ∀ i : Fin (m+1), colexANat K (i.val+1) ≠ 0 := by
    intro i
    unfold colexANat
    have hn : (0:ℝ) ≤ Nat.choose (i.val+1+1) 2 := by positivity
    linarith
  have hduality := weighted_duality_sq (fun i => colexANat K (i.val+1)) x v hP
  have hqv : q = x ⬝ᵥ v := by dsimp [q,A]; rw [hsolve]
  have hreserve := flattened_colex_diagonal_reserve hm hK hlarge r hr x
  have hbound := mul_le_mul_of_nonneg_right hreserve hC
  have hsq : q*q ≤ q*(144*(K+(m+1:ℕ))*C) := by
    rw [← hqv] at hduality
    dsimp [q,A,C] at *
    nlinarith
  change q ≤ 144*(K+(m+1:ℕ))*C
  rcases eq_or_lt_of_le hq0 with hzero | hpos
  · rw [← hzero]; positivity
  · exact le_of_mul_le_mul_left hsq hpos

/-- Whole coefficient-matrix version: the inequality holds for every vector
of column coefficients, for the single linear solution X=A^{-1}Z. -/
theorem flattened_colex_whole_solve_energy {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16)
    {σ : Type*} [Fintype σ] (Z : Matrix (Fin (m+1)) σ ℝ) :
    ∃ X : Matrix (Fin (m+1)) σ ℝ,
      incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) * X = Z ∧
      ∀ t : σ → ℝ,
        (X *ᵥ t) ⬝ᵥ (incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ (X *ᵥ t)) ≤
          144*(K+(m+1:ℕ)) * ∑ i, ((Z *ᵥ t) i / colexANat K (i.val+1))^2 := by
  let A := incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r)
  have hA : A.PosDef := flattened_colex_posDef hm hK hlarge r hr
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  let X := A⁻¹ * Z
  have hX : A*X=Z := by
    dsimp [X]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hdet, Matrix.one_mul]
  refine ⟨X, hX, ?_⟩
  intro t
  apply flattened_colex_edge_solve_energy hm hK hlarge r hr
  change A *ᵥ (X *ᵥ t) = Z *ᵥ t
  rw [Matrix.mulVec_mulVec, hX]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
