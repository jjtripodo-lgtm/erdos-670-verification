module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.PotentialSolve

@[expose] public section

open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma gram_linear_combination_projection {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (x : ι → ℝ) (i : ι) :
    inner ℝ (v i) (∑ j, x j • v j) = (Matrix.gram ℝ v *ᵥ x) i := by
  simp [inner_sum, real_inner_smul_right, Matrix.mulVec, dotProduct,
    Matrix.gram_apply, mul_comm]

lemma gram_linear_combination_norm_sq {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (x : ι → ℝ) :
    ‖∑ j, x j • v j‖^2 = x ⬝ᵥ (Matrix.gram ℝ v *ᵥ x) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, real_inner_smul_left,
    gram_linear_combination_projection, dotProduct]

/-- A single actual Euclidean edge frame supports every potential solve with
the uniform norm bound. The frame is independent and its dimension is fixed
by the macro count; no geometric or norm-control premise is assumed. -/
theorem flattened_colex_geometric_potentials {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) :
    ∃ v : Fin (m+1) → EuclideanSpace ℝ (Fin (m+1)),
      Matrix.gram ℝ v = incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) ∧
      LinearIndependent ℝ v ∧
      ∀ z : Fin (m+2) → ℝ, ∃ w : EuclideanSpace ℝ (Fin (m+1)),
        (∀ i, inner ℝ (v i) w = (pathIncidence (m+1) *ᵥ z) i) ∧
        ‖w‖^2 ≤ 16*∑ a, (z a / macroVertexWeight K a)^2 := by
  obtain ⟨v,hv,hli⟩ := posDef_exists_euclidean_independent_gram _
    (flattened_colex_posDef hm hK hlarge r hr)
  refine ⟨v,hv,hli,?_⟩
  intro z
  obtain ⟨x,hx,henergy⟩ := flattened_colex_potential_solve hm hK hlarge r hr z
  refine ⟨∑ j, x j • v j, ?_, ?_⟩
  · intro i
    rw [gram_linear_combination_projection, hv, hx]
  · rw [gram_linear_combination_norm_sq, hv]
    exact henergy

/-- The same frame also realizes a whole solution matrix, with one vector per
column and a simultaneous bound on every linear combination of those vectors. -/
theorem flattened_colex_geometric_whole_solve {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16)
    {σ : Type*} [Fintype σ] (Z : Matrix (Fin (m+1)) σ ℝ) :
    ∃ v : Fin (m+1) → EuclideanSpace ℝ (Fin (m+1)),
    ∃ w : σ → EuclideanSpace ℝ (Fin (m+1)),
      Matrix.gram ℝ v = incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) ∧
      (∀ i a, inner ℝ (v i) (w a) = Z i a) ∧
      ∀ t : σ → ℝ, ‖∑ a, t a • w a‖^2 ≤
        144*(K+(m+1:ℕ)) * ∑ i, ((Z *ᵥ t) i / colexANat K (i.val+1))^2 := by
  obtain ⟨v,hv,_⟩ := posDef_exists_euclidean_independent_gram _
    (flattened_colex_posDef hm hK hlarge r hr)
  obtain ⟨X,hX,hbound⟩ := flattened_colex_whole_solve_energy hm hK hlarge r hr Z
  let w : σ → EuclideanSpace ℝ (Fin (m+1)) := fun a => ∑ j, X j a • v j
  refine ⟨v,w,hv,?_,?_⟩
  · intro i a
    dsimp [w]
    rw [gram_linear_combination_projection, hv]
    have hh := congrFun (congrFun hX i) a
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hh
  · intro t
    have hw : ∑ a, t a • w a = ∑ j, (X *ᵥ t) j • v j := by
      simp only [w, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
        Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_comm]
    rw [hw, gram_linear_combination_norm_sq, hv]
    exact hbound t


lemma gram_increments_of_sq_distances {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Fin (n+1) → E) (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ i j, ‖p j-p i‖^2 = D i j) :
    Matrix.gram ℝ (fun i : Fin n => p i.succ-p i.castSucc) = incrementGram D := by
  ext i j
  have h11 := hD i.succ j.succ
  have h10 := hD i.succ j.castSucc
  have h01 := hD i.castSucc j.succ
  have h00 := hD i.castSucc j.castSucc
  simp only [norm_sub_sq_real] at h11 h10 h01 h00
  simp only [Matrix.gram_apply, incrementGram, inner_sub_left, inner_sub_right]
  nlinarith [real_inner_comm (p i.succ) (p j.succ),
    real_inner_comm (p i.succ) (p j.castSucc),
    real_inner_comm (p i.castSucc) (p j.succ),
    real_inner_comm (p i.castSucc) (p j.castSucc)]

lemma pathIncidence_mulVec_eq (n : ℕ) (z : Fin (n+1) → ℝ) (i : Fin n) :
    (pathIncidence n *ᵥ z) i = z i.castSucc-z i.succ := by
  simp [pathIncidence, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

lemma consecutive_potential_constant {n : ℕ} (a z : Fin (n+1) → ℝ)
    (h : ∀ i : Fin n, a i.succ-a i.castSucc = z i.castSucc-z i.succ)
    (j : Fin (n+1)) : a j+z j = a 0+z 0 := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i hi => have hh := h i; linarith

/-- Actual flattened macro points admit the arbitrary-anchor potential solve
in the SAME realization, with its quantitative norm bound. -/
theorem flattened_colex_all_anchor_potentials {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) :
    ∃ p : Fin (m+2) → EuclideanSpace ℝ (Fin (m+1)),
      AffineIndependent ℝ p ∧
      (∀ i j, ‖p j-p i‖^2 = offDiagonalShift (colexSqData (m:=m+1) K) r i j) ∧
      ∀ (a : Fin (m+2)) (z : Fin (m+2) → ℝ), z a=0 →
        ∃ w : EuclideanSpace ℝ (Fin (m+1)),
          (∀ j, inner ℝ (p a-p j) w = z j) ∧
          ‖w‖^2 ≤ 16*∑ j, (z j / macroVertexWeight K j)^2 := by
  obtain ⟨p,hpa,hpd⟩ := flattened_colex_realizes hm hK hlarge r hr
  let v : Fin (m+1) → EuclideanSpace ℝ (Fin (m+1)) :=
    fun i => p i.succ-p i.castSucc
  have hv : Matrix.gram ℝ v = incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) :=
    gram_increments_of_sq_distances p _ hpd
  refine ⟨p,hpa,hpd,?_⟩
  intro a z hza
  obtain ⟨x,hx,henergy⟩ := flattened_colex_potential_solve hm hK hlarge r hr z
  let w := ∑ j, x j • v j
  have hedges : ∀ i : Fin (m+1),
      inner ℝ (p i.succ) w-inner ℝ (p i.castSucc) w = z i.castSucc-z i.succ := by
    intro i
    rw [← inner_sub_left]
    change inner ℝ (v i) (∑ j, x j • v j) = _
    rw [gram_linear_combination_projection, hv, hx, pathIncidence_mulVec_eq]
  refine ⟨w,?_,?_⟩
  · intro j
    have ha := consecutive_potential_constant (fun b => inner ℝ (p b) w) z hedges a
    have hj := consecutive_potential_constant (fun b => inner ℝ (p b) w) z hedges j
    rw [inner_sub_left]
    rw [hza] at ha
    linarith
  · dsimp [w]
    rw [gram_linear_combination_norm_sq, hv]
    exact henergy


/-- Whole-matrix norm control inside any actual realization of the flattened
macro distances, so changing anchors does not require changing the embedding. -/
theorem whole_solve_in_flattened_realization {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16)
    (p : Fin (m+2) → EuclideanSpace ℝ (Fin (m+1)))
    (hpd : ∀ i j, ‖p j-p i‖^2 = offDiagonalShift (colexSqData (m:=m+1) K) r i j)
    {σ : Type*} [Fintype σ] (Z : Matrix (Fin (m+1)) σ ℝ) :
    ∃ w : σ → EuclideanSpace ℝ (Fin (m+1)),
      (∀ i a, inner ℝ (p i.succ-p i.castSucc) (w a) = Z i a) ∧
      ∀ t : σ → ℝ, ‖∑ a, t a • w a‖^2 ≤
        144*(K+(m+1:ℕ)) * ∑ i, ((Z *ᵥ t) i / colexANat K (i.val+1))^2 := by
  let v : Fin (m+1) → EuclideanSpace ℝ (Fin (m+1)) :=
    fun i => p i.succ-p i.castSucc
  have hv : Matrix.gram ℝ v = incrementGram (offDiagonalShift (colexSqData (m:=m+1) K) r) :=
    gram_increments_of_sq_distances p _ hpd
  obtain ⟨X,hX,hbound⟩ := flattened_colex_whole_solve_energy hm hK hlarge r hr Z
  let w : σ → EuclideanSpace ℝ (Fin (m+1)) := fun a => ∑ j, X j a • v j
  refine ⟨w,?_,?_⟩
  · intro i a
    change inner ℝ (v i) (∑ j, X j a • v j) = _
    rw [gram_linear_combination_projection, hv]
    have hh := congrFun (congrFun hX i) a
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hh
  · intro t
    have hw : ∑ a, t a • w a = ∑ j, (X *ᵥ t) j • v j := by
      simp only [w, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
        Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_comm]
    rw [hw, gram_linear_combination_norm_sq, hv]
    exact hbound t

/-- One actual macro configuration simultaneously supports all anchors and all
coefficient matrices with both quantitative solve bounds. Only scalar offset
and radius hypotheses remain. -/
theorem flattened_colex_unified_macro_model {m : ℕ} (hm : 1 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (m+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16) {σ : Type*} [Fintype σ] :
    ∃ p : Fin (m+2) → EuclideanSpace ℝ (Fin (m+1)),
      AffineIndependent ℝ p ∧
      (∀ i j, ‖p j-p i‖^2 = offDiagonalShift (colexSqData (m:=m+1) K) r i j) ∧
      (∀ (a : Fin (m+2)) (z : Fin (m+2) → ℝ), z a=0 →
        ∃ w : EuclideanSpace ℝ (Fin (m+1)),
          (∀ j, inner ℝ (p a-p j) w = z j) ∧
          ‖w‖^2 ≤ 16*∑ j, (z j / macroVertexWeight K j)^2) ∧
      (∀ Z : Matrix (Fin (m+1)) σ ℝ,
        ∃ w : σ → EuclideanSpace ℝ (Fin (m+1)),
          (∀ i a, inner ℝ (p i.succ-p i.castSucc) (w a) = Z i a) ∧
          ∀ t : σ → ℝ, ‖∑ a, t a • w a‖^2 ≤
            144*(K+(m+1:ℕ)) * ∑ i, ((Z *ᵥ t) i / colexANat K (i.val+1))^2) := by
  obtain ⟨p,hpa,hpd,hanchor⟩ := flattened_colex_all_anchor_potentials hm hK hlarge r hr
  exact ⟨p,hpa,hpd,hanchor,fun Z => whole_solve_in_flattened_realization hm hK hlarge r hr p hpd Z⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension
