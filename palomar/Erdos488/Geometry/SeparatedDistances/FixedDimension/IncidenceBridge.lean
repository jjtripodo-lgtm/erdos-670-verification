module

public import Erdos488.Geometry.SeparatedDistances.Defs
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.Flattening
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.ColexReserve
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.ColexReserveDirectCS

@[expose] public section

open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Consecutive vertex-incidence rows, with the orientation used in the paper. -/
def pathIncidence (m : ℕ) : Matrix (Fin m) (Fin (m+1)) ℝ :=
  fun i a => (if a=i.castSucc then 1 else 0) - (if a=i.succ then 1 else 0)

lemma pathIncidence_row_sum (m : ℕ) (i : Fin m) :
    ∑ a, pathIncidence m i a = 0 := by
  simp [pathIncidence, Finset.sum_sub_distrib]

/-- The existing literal incrementGram definition is the conditional distance
Gram of the actual consecutive-incidence matrix. -/
theorem incrementGram_eq_incidence (m : ℕ) (D : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) :
    incrementGram D = -(1/2 : ℝ) • (pathIncidence m * D * (pathIncidence m)ᵀ) := by
  ext i j
  simp [incrementGram, pathIncidence, Matrix.mul_apply, Matrix.transpose_apply,
    sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

lemma pathIncidence_transpose_mulVec_sum (m : ℕ) (x : Fin m → ℝ) :
    ∑ a, ((pathIncidence m)ᵀ *ᵥ x) a = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, pathIncidence_row_sum]


lemma dotProduct_mulVec_eq_double_sum {ι : Type*} [Fintype ι]
    (D : Matrix ι ι ℝ) (z : ι → ℝ) :
    z ⬝ᵥ (D *ᵥ z) = ∑ i, ∑ j, z i * D i j * z j := by
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem incrementGram_quadratic_eq_incidence (m : ℕ)
    (D : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (incrementGram D *ᵥ x) = -(1/2 : ℝ) *
      (((pathIncidence m)ᵀ *ᵥ x) ⬝ᵥ (D *ᵥ ((pathIncidence m)ᵀ *ᵥ x))) := by
  rw [incrementGram_eq_incidence, Matrix.smul_mulVec, dotProduct_smul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose]
  rfl

/-- Exact conditional-Gram subtraction, using the literal incidence matrix and
OFF-diagonal shift. No Euclidean-realizability assumption is used. -/
theorem flattened_incrementGram_quadratic (m : ℕ)
    (D : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (hdiag : ∀ i, D i i = 0)
    (r : ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (incrementGram (offDiagonalShift D r) *ᵥ x) =
      x ⬝ᵥ (incrementGram D *ᵥ x) -
        r * ∑ a, (((pathIncidence m)ᵀ *ᵥ x) a)^2 := by
  rw [incrementGram_quadratic_eq_incidence, incrementGram_quadratic_eq_incidence,
    dotProduct_mulVec_eq_double_sum, dotProduct_mulVec_eq_double_sum,
    offDiagonalShift_zero_sum_quadratic D hdiag r _
      (pathIncidence_transpose_mulVec_sum m x)]
  ring



lemma pathIncidence_zero_coordinate (m : ℕ) (x : Fin (m+1) → ℝ) :
    ((pathIncidence (m+1))ᵀ *ᵥ x) 0 = x 0 := by
  have hfirst : ∀ i : Fin (m+1), ((0 : Fin (m+2)) = i.castSucc) ↔ i=0 := by
    intro i
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [Fin.val_zero, Fin.val_castSucc]
    omega
  have hsecond : ∀ i : Fin (m+1), ¬((0 : Fin (m+2)) = i.succ) := by
    intro i h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, pathIncidence,
    sub_mul, Finset.sum_sub_distrib, hfirst, hsecond, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_false,
    Finset.sum_const_zero, sub_zero]

lemma pathIncidence_last_coordinate (m : ℕ) (x : Fin (m+1) → ℝ) :
    ((pathIncidence (m+1))ᵀ *ᵥ x) (Fin.last (m+1)) = -x (Fin.last m) := by
  have hfirst : ∀ i : Fin (m+1), ¬ Fin.last (m+1) = i.castSucc := by
    intro i h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  have hsecond : ∀ i : Fin (m+1), (Fin.last (m+1) = i.succ) ↔ i=Fin.last m := by
    intro i
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [Fin.val_last, Fin.val_succ]
    omega
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, pathIncidence,
    sub_mul, Finset.sum_sub_distrib, hfirst, hsecond, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_false,
    Finset.sum_const_zero, zero_sub, neg_mul, Finset.sum_neg_distrib]

lemma pathIncidence_internal_coordinate (m : ℕ) (x : Fin (m+1) → ℝ) (i : Fin m) :
    ((pathIncidence (m+1))ᵀ *ᵥ x) i.succ.castSucc = x i.succ - x i.castSucc := by
  have hfirst : ∀ j : Fin (m+1), (i.succ.castSucc = j.castSucc) ↔ j=i.succ := by
    intro j
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have hsecond : ∀ j : Fin (m+1), (i.succ.castSucc = j.succ) ↔ j=i.castSucc := by
    intro j
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, pathIncidence,
    sub_mul, Finset.sum_sub_distrib, hfirst, hsecond, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]


/-- The quadratic energy of the actual incidence transpose, including both
boundary coordinates. -/
theorem weighted_pathIncidence_energy (m : ℕ)
    (w : Fin (m+2) → ℝ) (x : Fin (m+1) → ℝ) :
    (∑ a, w a * (((pathIncidence (m+1))ᵀ *ᵥ x) a)^2) =
      w 0 * x 0 ^ 2 +
      (∑ i : Fin m, w i.succ.castSucc * (x i.castSucc - x i.succ)^2) +
      w (Fin.last (m+1)) * x (Fin.last m)^2 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, pathIncidence_zero_coordinate,
    pathIncidence_internal_coordinate, pathIncidence_last_coordinate, neg_sq]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  ring

noncomputable def macroVertexWeight {m : ℕ} (K : ℝ) (a : Fin (m+1)) : ℝ :=
  colexANat K (if a.val=0 then 1 else a.val)

/-- Literal incidence formulation of the weighted colex tridiagonal reserve. -/
theorem colex_tridiagonal_ge_incidence_weight {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K) (x : Fin (m+1) → ℝ) :
    (1/4 : ℝ) * (∑ a : Fin (m+2), macroVertexWeight K a ^ 2 *
        (((pathIncidence (m+1))ᵀ *ᵥ x) a)^2) ≤
      x ⬝ᵥ (colexTridiagonal K *ᵥ x) := by
  rw [weighted_pathIncidence_energy]
  have ht := colex_tridiagonal_ge_quarter_weighted_path (m:=m+1) (by omega) hK x
  simp only [macroVertexWeight, Fin.val_zero, ↓reduceIte, Fin.val_last,
    Fin.val_castSucc, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ite_false] at *
  simp only [Nat.add_sub_cancel, star_trivial] at ht
  change colexANat K 1 ^ 2 / 4 * x 0 ^ 2 +
    (∑ i : Fin m, colexANat K (i.val+1)^2 / 4 * (x i.castSucc - x i.succ)^2) +
    colexANat K (m+1)^2 / 4 * x (Fin.last m)^2 ≤ _ at ht
  simp only [mul_add, Finset.mul_sum]
  convert ht using 1 <;> ring_nf


lemma macroVertexWeight_ge_K {m : ℕ} (K : ℝ) (a : Fin (m+1)) :
    K ≤ macroVertexWeight K a := by
  unfold macroVertexWeight colexANat
  have h : (0:ℝ) ≤ Nat.choose ((if a.val=0 then 1 else a.val)+1) 2 := by positivity
  linarith

/-- Both actual flattened colex reserves. Here there are m+2 macro vertices,
m+1 increments, and r is the squared radius to subtract. -/
theorem flattened_colex_two_reserves {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) (x : Fin (m+1) → ℝ) :
    (1/16 : ℝ) * (∑ a : Fin (m+2), macroVertexWeight K a ^ 2 *
        (((pathIncidence (m+1))ᵀ *ᵥ x) a)^2) ≤
      x ⬝ᵥ (incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ x) ∧
    (1/4 : ℝ) * (x ⬝ᵥ (colexTridiagonal K *ᵥ x)) ≤
      x ⬝ᵥ (incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ x) := by
  let z := (pathIncidence (m+1))ᵀ *ᵥ x
  have hL : 0 ≤ ∑ a, (z a)^2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hW : K^2 * (∑ a, (z a)^2) ≤
      ∑ a, macroVertexWeight K a ^ 2 * (z a)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hp := macroVertexWeight_ge_K K a
    have hsq : K^2 ≤ macroVertexWeight K a ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hG := colex_incrementGram_ge_half_tridiagonal_direct
    (m:=m+1) (by omega) hK hlarge x
  have hT := colex_tridiagonal_ge_incidence_weight hm hK x
  simp only [star_trivial] at hG
  have hh := radius_shift_preserves_two_reserves
    (x ⬝ᵥ (incrementGram (colexSqData (m:=m+1) K) *ᵥ x))
    (x ⬝ᵥ (colexTridiagonal K *ᵥ x))
    (∑ a, macroVertexWeight K a ^ 2 * (z a)^2)
    (∑ a, (z a)^2) r K hL (by linarith) (by dsimp [z]; linarith) hW hr
  rw [flattened_incrementGram_quadratic (m+1) _ (colexSqData_diag K)]
  dsimp [z] at hh
  constructor <;> linarith [hh.1, hh.2]


lemma offDiagonalShift_isHermitian {ι : Type*} [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hD : D.IsHermitian) (r : ℝ) :
    (offDiagonalShift D r).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  by_cases h : i=j
  · subst j; rfl
  · have hh := hD.apply i j
    simp only [star_trivial] at hh
    simp only [offDiagonalShift, h, Ne.symm h, ite_false]
    rw [hh]

/-- The complementary diagonal lower bound for the actual flattened Gram. -/
theorem flattened_colex_diagonal_reserve {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) (x : Fin (m+1) → ℝ) :
    (∑ i, colexANat K (i.val+1)^2 * x i ^ 2) ≤
      144*(K+(m+1 : ℕ)) *
        (x ⬝ᵥ (incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) *ᵥ x)) := by
  have ht := colex_tridiagonal_ge_adjacent_diagonal (m:=m+1) (by omega) hK x
  have hf := (flattened_colex_two_reserves hm hK hlarge r hr x).2
  have hc : 0 ≤ 144*(K+(m+1 : ℕ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hf hc
  simp only [star_trivial] at ht
  nlinarith

/-- Strict positive definiteness of the actual flattened colex increment Gram.
All hypotheses are explicit scalar bounds; realizability is not assumed. -/
theorem flattened_colex_posDef {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) :
    (incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (incrementGram_isHermitian _
      (offDiagonalShift_isHermitian _ (colexSqData_isHermitian K) r))
  intro x hx
  have hp := colexQ_pos hK hx
  have ht := colex_tridiagonal_ge_Q (m:=m+1) (by omega) hK x
  have hf := (flattened_colex_two_reserves hm hK hlarge r hr x).2
  simp only [star_trivial] at ht ⊢
  nlinarith


/-- The flattened macro squared distances are actually realized by affinely
independent points in the exact (vertex count minus one) Euclidean dimension. -/
theorem flattened_colex_realizes {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) :
    ∃ p : Fin (m+2) → EuclideanSpace ℝ (Fin (m+1)),
      AffineIndependent ℝ p ∧ ∀ i j,
        ‖p j-p i‖^2 = offDiagonalShift (colexSqData (m:=m+1) K) r i j := by
  exact posDef_incrementGram_realizes_in_euclideanSpace _
    (offDiagonalShift_isHermitian _ (colexSqData_isHermitian K) r)
    (fun i => by simp [offDiagonalShift])
    (flattened_colex_posDef hm hK hlarge r hr)

end Erdos488.Geometry.SeparatedDistances.FixedDimension
