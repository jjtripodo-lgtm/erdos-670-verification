module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceParameterBounds

@[expose] public section

/-! The two extraction columns of the rational quadratic coefficient family.
The reverse increment orientation agrees with the manuscript's `Z_B`; the
existing `whole_solve_in_flattened_realization` uses forward increments, so
its input is the negative of this matrix. -/

open scoped BigOperators Matrix
open Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Extract the anchor at the upper endpoint of a consecutive macro edge. -/
def sourceBPickUpper (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+2)) ℝ :=
  fun i A => if A = i.succ then 1 else 0

/-- Extract the anchor at the lower endpoint of a consecutive macro edge. -/
def sourceBPickLower (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+2)) ℝ :=
  fun i A => if A = i.castSucc then 1 else 0

/-- The paper's reverse-oriented consecutive projection matrix, `-aP+bQ`. -/
noncomputable def sourceBReverseMatrix (n k : ℕ) : Matrix (Fin (n+1)) (Fin (n+2)) ℝ :=
  fun i A => -(64 / 9 : ℝ) * sourceBPickUpper n i A +
    (9 * (k : ℝ)^2) * sourceBPickLower n i A

lemma sourceBPickUpper_mulVec (n : ℕ) (x : Fin (n+2) → ℝ) (i : Fin (n+1)) :
    (sourceBPickUpper n *ᵥ x) i = x i.succ := by
  simp [sourceBPickUpper, Matrix.mulVec, dotProduct]

lemma sourceBPickLower_mulVec (n : ℕ) (x : Fin (n+2) → ℝ) (i : Fin (n+1)) :
    (sourceBPickLower n *ᵥ x) i = x i.castSucc := by
  simp [sourceBPickLower, Matrix.mulVec, dotProduct]

lemma sourceBReverseMatrix_mulVec (n k : ℕ)
    (x : Fin (n+2) → ℝ) (i : Fin (n+1)) :
    (sourceBReverseMatrix n k *ᵥ x) i =
      -(64 / 9 : ℝ) * x i.succ + (9 * (k : ℝ)^2) * x i.castSucc := by
  simp [sourceBReverseMatrix, sourceBPickUpper, sourceBPickLower,
    Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]

lemma sourceBPickUpper_contract (n : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+1), ((sourceBPickUpper n *ᵥ x) i)^2) ≤
      ∑ A : Fin (n+2), (x A)^2 := by
  simp_rw [sourceBPickUpper_mulVec]
  conv_rhs => rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg (x 0))

lemma sourceBPickLower_contract (n : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+1), ((sourceBPickLower n *ᵥ x) i)^2) ≤
      ∑ A : Fin (n+2), (x A)^2 := by
  simp_rw [sourceBPickLower_mulVec]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (sq_nonneg (x (Fin.last (n+1))))

/-- The exact two-extraction operator estimate, stated as a quadratic form. -/
theorem sourceBReverseMatrix_sq_bound (n k : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+1), (sourceBReverseMatrix n k *ᵥ x) i ^ 2) ≤
      ((64 / 9 : ℝ) + 9 * (k : ℝ)^2)^2 *
        ∑ A : Fin (n+2), x A ^ 2 := by
  let a : ℝ := 64 / 9
  let b : ℝ := 9 * (k : ℝ)^2
  have ha : 0 ≤ a := by dsimp [a]; norm_num
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hrow (i : Fin (n+1)) :
      (sourceBReverseMatrix n k *ᵥ x) i ^ 2 ≤
        (a+b) * (a * x i.succ ^ 2 + b * x i.castSucc ^ 2) := by
    rw [sourceBReverseMatrix_mulVec]
    have hid : (a+b) * (a * x i.succ ^ 2 + b * x i.castSucc ^ 2) -
        (-a*x i.succ+b*x i.castSucc)^2 =
          a*b*(x i.succ+x i.castSucc)^2 := by ring
    have hnonneg : 0 ≤ a*b*(x i.succ+x i.castSucc)^2 := by positivity
    dsimp [a,b] at hid
    nlinarith only [hid, hnonneg]
  have hup : (∑ i : Fin (n+1), x i.succ ^ 2) ≤
      ∑ A : Fin (n+2), x A ^ 2 := by
    simpa only [sourceBPickUpper_mulVec] using sourceBPickUpper_contract n x
  have hlo : (∑ i : Fin (n+1), x i.castSucc ^ 2) ≤
      ∑ A : Fin (n+2), x A ^ 2 := by
    simpa only [sourceBPickLower_mulVec] using sourceBPickLower_contract n x
  calc
    _ ≤ ∑ i : Fin (n+1),
        (a+b) * (a*x i.succ^2+b*x i.castSucc^2) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (a+b) * (a*(∑ i : Fin (n+1), x i.succ^2) +
        b*(∑ i : Fin (n+1), x i.castSucc^2)) := by
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ (a+b) * (a*(∑ A : Fin (n+2), x A^2) +
        b*(∑ A : Fin (n+2), x A^2)) := by
      apply mul_le_mul_of_nonneg_left _ (add_nonneg ha hb)
      exact add_le_add (mul_le_mul_of_nonneg_left hup ha)
        (mul_le_mul_of_nonneg_left hlo hb)
    _ = _ := by dsimp [a,b]; ring

theorem sourceBReverseMatrix_weighted_sq_bound (n k : ℕ) {K : ℝ}
    (hK : 0 < K) (x : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+1),
      ((sourceBReverseMatrix n k *ᵥ x) i /
        colexANat K (i.val+1))^2) ≤
      (((64 / 9 : ℝ) + 9*(k : ℝ)^2)/K)^2 *
        ∑ A : Fin (n+2), x A^2 := by
  have hweight (i : Fin (n+1)) : K ≤ colexANat K (i.val+1) := by
    unfold colexANat
    have hchoose : (0 : ℝ) ≤ Nat.choose (i.val+1+1) 2 := by positivity
    linarith
  have hterm (i : Fin (n+1)) :
      ((sourceBReverseMatrix n k *ᵥ x) i / colexANat K (i.val+1))^2 ≤
        ((sourceBReverseMatrix n k *ᵥ x) i / K)^2 := by
    have hp : 0 < colexANat K (i.val+1) := lt_of_lt_of_le hK (hweight i)
    have hs : K^2 ≤ (colexANat K (i.val+1))^2 := by nlinarith [hweight i]
    rw [div_pow, div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos hK)).2
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  calc
    _ ≤ ∑ i : Fin (n+1), ((sourceBReverseMatrix n k *ᵥ x) i / K)^2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i : Fin (n+1), (sourceBReverseMatrix n k *ᵥ x) i^2) / K^2 := by
      simp only [div_pow, Finset.sum_div]
    _ ≤ (((64 / 9 : ℝ) + 9*(k : ℝ)^2)^2 *
        ∑ A : Fin (n+2), x A^2) / K^2 := by
      gcongr
      exact sourceBReverseMatrix_sq_bound n k x
    _ = _ := by ring

/-- In the source range, the paper's convenient `18k²/K` estimate follows. -/
theorem sourceBReverseMatrix_weighted_18_bound (n k : ℕ) (hk : 2 ≤ k)
    {K : ℝ} (hK : 0 < K) (x : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+1),
      ((sourceBReverseMatrix n k *ᵥ x) i /
        colexANat K (i.val+1))^2) ≤
      (18*(k : ℝ)^2/K)^2 * ∑ A : Fin (n+2), x A^2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoeff : (64/9 : ℝ)+9*(k : ℝ)^2 ≤ 18*(k : ℝ)^2 := by
    nlinarith [sq_nonneg ((k : ℝ)-2)]
  have hnonneg : 0 ≤ (64/9 : ℝ)+9*(k : ℝ)^2 := by positivity
  have hsq : (((64/9 : ℝ)+9*(k : ℝ)^2)/K)^2 ≤
      (18*(k : ℝ)^2/K)^2 := by
    have hd : ((64/9 : ℝ)+9*(k : ℝ)^2)/K ≤
        18*(k : ℝ)^2/K := div_le_div_of_nonneg_right hcoeff (le_of_lt hK)
    nlinarith [div_nonneg hnonneg (le_of_lt hK)]
  calc
    _ ≤ (((64/9 : ℝ)+9*(k : ℝ)^2)/K)^2 *
        ∑ A : Fin (n+2), x A^2 :=
      sourceBReverseMatrix_weighted_sq_bound n k hK x
    _ ≤ (18*(k : ℝ)^2/K)^2 * ∑ A : Fin (n+2), x A^2 :=
      mul_le_mul_of_nonneg_right hsq (Finset.sum_nonneg fun A _ => sq_nonneg _)

/-- The matrix is the reverse difference of the actual rational anchor
potential, including the endpoint columns. -/
theorem sourceBReverseMatrix_eq_potential_difference (n k : ℕ)
    (i : Fin (n+1)) (A : Fin (n+2)) :
    sourceBReverseMatrix n k i A =
      sourceQuadraticPotential k A i.succ -
        sourceQuadraticPotential k A i.castSucc := by
  unfold sourceBReverseMatrix sourceBPickUpper sourceBPickLower
    sourceQuadraticPotential
  split_ifs <;> simp only [Fin.val_succ, Fin.val_castSucc, Fin.ext_iff] at *
    <;> first | omega | ring

/-- The existing whole solve, instantiated with the *actual* consecutive
quadratic-potential matrix. Its forward-edge input is `-Z_B`. -/
theorem sourceBQuadraticCoefficients_whole_solve {n k : ℕ} (hn : 1 ≤ n)
    (hk : 2 ≤ k) {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (n+2) : ℝ)^2 ≤ K)
    (r : ℝ) (hr : r ≤ K^2/16)
    (p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hpd : ∀ i j, ‖p j-p i‖^2 =
      offDiagonalShift (colexSqData (m:=n+1) K) r i j) :
    ∃ B : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
      (∀ A J, inner ℝ (p A-p J) (B A) = sourceQuadraticPotential k A J) ∧
      (∀ t : Fin (n+2) → ℝ,
        ‖∑ A, t A • B A‖^2 ≤
          144*(K+(n+1:ℕ))*(18*(k : ℝ)^2/K)^2 *
            ∑ A, t A^2) := by
  let Z : Matrix (Fin (n+1)) (Fin (n+2)) ℝ :=
    fun i A => -sourceBReverseMatrix n k i A
  obtain ⟨B, hproj, henergy⟩ :=
    whole_solve_in_flattened_realization hn hK hlarge r hr p hpd Z
  refine ⟨B, ?_, ?_⟩
  · intro A J
    have hedges (i : Fin (n+1)) :
        inner ℝ (p i.succ) (B A) - inner ℝ (p i.castSucc) (B A) =
          sourceQuadraticPotential k A i.castSucc -
            sourceQuadraticPotential k A i.succ := by
      have h := hproj i A
      rw [inner_sub_left] at h
      change _ = -sourceBReverseMatrix n k i A at h
      rw [sourceBReverseMatrix_eq_potential_difference] at h
      linarith
    have ha := consecutive_potential_constant
      (fun j => inner ℝ (p j) (B A)) (sourceQuadraticPotential k A) hedges A
    have hj := consecutive_potential_constant
      (fun j => inner ℝ (p j) (B A)) (sourceQuadraticPotential k A) hedges J
    rw [sourceQuadraticPotential_self] at ha
    rw [inner_sub_left]
    linarith
  · intro t
    have hZ (i : Fin (n+1)) :
        (Z *ᵥ t) i = -(sourceBReverseMatrix n k *ᵥ t) i := by
      simp only [Z, Matrix.mulVec, dotProduct, neg_mul,
        Finset.sum_neg_distrib]
    have hweighted := sourceBReverseMatrix_weighted_18_bound n k hk
      (by linarith : 0 < K) t
    calc
      ‖∑ A, t A • B A‖^2 ≤
          144*(K+(n+1:ℕ)) *
            ∑ i, ((Z *ᵥ t) i / colexANat K (i.val+1))^2 := henergy t
      _ = 144*(K+(n+1:ℕ)) *
            ∑ i, ((sourceBReverseMatrix n k *ᵥ t) i /
              colexANat K (i.val+1))^2 := by simp only [hZ, neg_div, even_two, Even.neg_pow]
      _ ≤ 144*(K+(n+1:ℕ)) *
            ((18*(k : ℝ)^2/K)^2 * ∑ A, t A^2) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ = _ := by ring

/-- The whole-solve B estimate fits *each* of the two equal quadratic
completion budgets, using the actual ceiling offset and source range. -/
theorem sourceBQuadraticScalar_budget {n k : ℕ} (hm : 34000 ≤ n+2) :
    3*(144*((sourceOffset (n+2) : ℝ)+(n+1:ℕ)) *
      (18*(k : ℝ)^2/(sourceOffset (n+2) : ℝ))^2) ≤
      sourceReserve0Sq (n+2) k := by
  have hupper := sourceOffset_plus_m_upper (n+2) hm
  have hcount : (((n+1 : ℕ) : ℝ) ≤ (n+2:ℕ)) := by
    exact_mod_cast (show n+1 ≤ n+2 by omega)
  have hmid : (sourceOffset (n+2) : ℝ)+(n+1:ℕ) ≤
      ((n+2:ℕ) : ℝ)^2/63 := by linarith
  have hfactor : 144*((sourceOffset (n+2) : ℝ)+(n+1:ℕ)) ≤
      4*((n+2:ℕ) : ℝ)^2 := by
    have hscaled := mul_le_mul_of_nonneg_left hmid
      (by norm_num : (0 : ℝ) ≤ 144)
    nlinarith only [hscaled, sq_nonneg (((n+2:ℕ) : ℝ))]
  have hfactor' := mul_le_mul_of_nonneg_right hfactor
    (sq_nonneg (18*(k : ℝ)^2/(sourceOffset (n+2) : ℝ)))
  calc
    _ = 3*((144*((sourceOffset (n+2) : ℝ)+(n+1:ℕ))) *
        (18*(k : ℝ)^2/(sourceOffset (n+2) : ℝ))^2) := by ring
    _ ≤ 3*((4*((n+2:ℕ) : ℝ)^2) *
        (18*(k : ℝ)^2/(sourceOffset (n+2) : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hfactor' (by norm_num)
    _ = sourceReserve0Sq (n+2) k := by
      unfold sourceReserve0Sq
      ring

/-- Same-index vectors for the actual flattened source centers, with their
quadratic projections and a whole-family bound in the paper's `b₀²/3 = b₂²/3`
completion budget. -/
theorem sourceBQuadraticCoefficients_source_budget {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k)
    (p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hpd : ∀ i j, ‖p j-p i‖^2 =
      offDiagonalShift (colexSqData (m:=n+1)
        (sourceOffset (n+2) : ℝ))
        (sourceFlatteningRadius (n+2) k) i j) :
    ∃ B : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
      (∀ A J, inner ℝ (p A-p J) (B A) = sourceQuadraticPotential k A J) ∧
      (∀ t : Fin (n+2) → ℝ,
        3*‖∑ A, t A • B A‖^2 ≤
          sourceReserve0Sq (n+2) k * ∑ A, t A^2) := by
  obtain ⟨hK, hlarge, _, hr⟩ :=
    source_macro_operator_scalar_gates (n+2) k hm hk
  obtain ⟨B, hproj, hbound⟩ :=
    sourceBQuadraticCoefficients_whole_solve (by omega : 1 ≤ n)
      hk hK hlarge (sourceFlatteningRadius (n+2) k) hr p hpd
  refine ⟨B, hproj, ?_⟩
  intro t
  have hs := sourceBQuadraticScalar_budget (k:=k) hm
  have hsum : 0 ≤ ∑ A : Fin (n+2), t A^2 :=
    Finset.sum_nonneg (fun A _ => sq_nonneg _)
  calc
    3*‖∑ A, t A • B A‖^2 ≤
        3*((144*((sourceOffset (n+2) : ℝ)+(n+1:ℕ)) *
          (18*(k : ℝ)^2/(sourceOffset (n+2) : ℝ))^2) *
            ∑ A, t A^2) :=
      mul_le_mul_of_nonneg_left (hbound t) (by norm_num)
    _ = (3*(144*((sourceOffset (n+2) : ℝ)+(n+1:ℕ)) *
          (18*(k : ℝ)^2/(sourceOffset (n+2) : ℝ))^2)) *
            ∑ A, t A^2 := by ring
    _ ≤ sourceReserve0Sq (n+2) k * ∑ A, t A^2 :=
      mul_le_mul_of_nonneg_right hs hsum

/-- Squared form of the paper's `‖B‖op ≤ 36mk²/K`, for the same actual
coefficient family and every input. -/
theorem sourceBQuadraticCoefficients_source_36 {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k)
    (p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hpd : ∀ i j, ‖p j-p i‖^2 =
      offDiagonalShift (colexSqData (m:=n+1)
        (sourceOffset (n+2) : ℝ))
        (sourceFlatteningRadius (n+2) k) i j) :
    ∃ B : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
      (∀ A J, inner ℝ (p A-p J) (B A) = sourceQuadraticPotential k A J) ∧
      (∀ t : Fin (n+2) → ℝ,
        ‖∑ A, t A • B A‖^2 ≤
          (36*(n+2:ℕ)*(k : ℝ)^2/(sourceOffset (n+2) : ℝ))^2 *
            ∑ A, t A^2) := by
  obtain ⟨B, hproj, hbudget⟩ :=
    sourceBQuadraticCoefficients_source_budget hm hk p hpd
  refine ⟨B, hproj, ?_⟩
  intro t
  calc
    ‖∑ A, t A • B A‖^2 ≤
        sourceReserve0Sq (n+2) k / 3 * ∑ A, t A^2 := by
      have h := hbudget t
      nlinarith only [h]
    _ = _ := by unfold sourceReserve0Sq; ring

/-- In the actual full-dimensional macro realization, the prescribed
quadratic projections determine every coefficient vector uniquely. -/
theorem sourceBQuadraticCoefficients_unique {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k)
    (p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hpd : ∀ i j, ‖p j-p i‖^2 =
      offDiagonalShift (colexSqData (m:=n+1)
        (sourceOffset (n+2) : ℝ))
        (sourceFlatteningRadius (n+2) k) i j)
    (B C : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hB : ∀ A J, inner ℝ (p A-p J) (B A) = sourceQuadraticPotential k A J)
    (hC : ∀ A J, inner ℝ (p A-p J) (C A) = sourceQuadraticPotential k A J) :
    B = C := by
  obtain ⟨hK, hlarge, _, hr⟩ :=
    source_macro_operator_scalar_gates (n+2) k hm hk
  let v : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)) :=
    fun i => p i.succ-p i.castSucc
  have hv : Matrix.gram ℝ v =
      incrementGram (offDiagonalShift (colexSqData (m:=n+1)
        (sourceOffset (n+2) : ℝ)) (sourceFlatteningRadius (n+2) k)) :=
    gram_increments_of_sq_distances p _ hpd
  have hli : LinearIndependent ℝ v := by
    apply Matrix.linearIndependent_of_posDef_gram
    rw [hv]
    exact flattened_colex_posDef (by omega : 1 ≤ n) hK hlarge
      (sourceFlatteningRadius (n+2) k) hr
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  funext A
  have hedge (i : Fin (n+1)) :
      inner ℝ (v i) (B A) = inner ℝ (v i) (C A) := by
    have hb0 := hB A i.castSucc
    have hb1 := hB A i.succ
    have hc0 := hC A i.castSucc
    have hc1 := hC A i.succ
    dsimp [v]
    simp only [inner_sub_left] at *
    linarith
  apply ext_inner_left ℝ
  intro u
  have hu : u ∈ Submodule.span ℝ (Set.range v) := by
    rw [hspan]
    trivial
  induction hu using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hedge i
  | zero => simp
  | add u w _ _ hu hw => simpa only [inner_add_left] using congrArg₂ (· + ·) hu hw
  | smul a u _ hu => simpa only [real_inner_smul_left] using congrArg (a * ·) hu

/-- The bound applies to *any* B family already chosen by the source
completion theorem: its actual quadratic projections force equality with the
family constructed through the consecutive whole solve. -/
theorem sourceBExistingQuadraticCoefficients_budget {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k)
    (p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hpd : ∀ i j, ‖p j-p i‖^2 =
      offDiagonalShift (colexSqData (m:=n+1)
        (sourceOffset (n+2) : ℝ))
        (sourceFlatteningRadius (n+2) k) i j)
    (B : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hB : ∀ A J, inner ℝ (p A-p J) (B A) = sourceQuadraticPotential k A J)
    (t : Fin (n+2) → ℝ) :
    3*‖∑ A, t A • B A‖^2 ≤
      sourceReserve0Sq (n+2) k * ∑ A, t A^2 := by
  obtain ⟨C, hC, hbudget⟩ :=
    sourceBQuadraticCoefficients_source_budget hm hk p hpd
  have hBC := sourceBQuadraticCoefficients_unique hm hk p hpd B C hB hC
  rw [hBC]
  exact hbudget t

/-- Acyclic downstream assembly of the literal source operator. This uses
the two-diagonal *whole-matrix* quadratic B estimate when constructing the
residual Gram factor; the older per-column assembly remains available. -/
theorem source_actual_operator_completion_universal_B_matrix {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k) :
    ∃ p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ B : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ F G : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ V : Matrix (Fin (n+2) × Fin 5) (Fin (n+2) × Fin 5) ℝ,
      (∀ i j, ‖p j-p i‖ ^ 2 =
        offDiagonalShift (colexSqData (m:=n+1)
          (sourceOffset (n+2) : ℝ))
          (sourceFlatteningRadius (n+2) k) i j) ∧
      (∀ A J, inner ℝ (p A-p J) (B A) =
        sourceQuadraticPotential k A J) ∧
      (∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
        fineIncidence (n+1) (sourceOffset (n+2) : ℝ) i a) ∧
      (∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
        coarseIncidence (n+1) (sourceOffset (n+2) : ℝ) i a) ∧
      (sourceActiveMatrix k B F G)ᵀ * (sourceActiveMatrix k B F G) +
        Vᵀ * V =
        Matrix.diagonal (fun q : Fin (n+2) × Fin 5 =>
          trigWeight (sourceReserve0 (n+2) k)
            (sourceReserve1 (n+2) k)
            (sourceReserve0 (n+2) k) q.2) := by
  obtain ⟨hK, hlarge, hmacro, hr⟩ :=
    source_macro_operator_scalar_gates (n+2) k hm hk
  have hnK : (n+1 : ℕ) ≤ (sourceOffset (n+2) : ℝ) := by
    have hh : ((n+1 : ℕ) : ℝ) ≤ (n+2 : ℕ) := by
      exact_mod_cast (show n+1 ≤ n+2 by omega)
    linarith
  obtain ⟨p, _, hpd⟩ :=
    flattened_colex_realizes (by omega : 1 ≤ n) hK hlarge
      (sourceFlatteningRadius (n+2) k) hr
  obtain ⟨B, hBproj, hBbudget⟩ :=
    sourceBQuadraticCoefficients_source_budget hm hk p hpd
  obtain ⟨F, G, hFproj, hGproj, hFbudget, hGbudget⟩ :=
    sourceFineCoarseCoefficients_exist (by omega : 1 ≤ n) hK hlarge
      (sourceFlatteningRadius (n+2) k) hr hnK p hpd
  have hBnorm (t : Fin (n+2) → ℝ) :
      3 * ‖∑ A, t A • B A‖ ^ 2 ≤
        (sourceReserve0 (n+2) k) ^ 2 * ∑ A, t A ^ 2 := by
    rw [sourceReserve0_square]
    exact hBbudget t
  have hUnorm (t : Fin (n+2) → ℝ) :
      3 * ‖∑ A, t A • sourceSineCoefficient k F G A‖ ^ 2 ≤
        (sourceReserve1 (n+2) k) ^ 2 * ∑ A, t A ^ 2 := by
    rw [sourceReserve1_square]
    exact sourceSineCoefficients_whole_budget k hm hk F G
      hFbudget hGbudget t
  obtain ⟨V, hV⟩ := source_three_group_completion_factor B
    (sourceSineCoefficient k F G)
    (sourceReserve0 (n+2) k) (sourceReserve1 (n+2) k)
    hBnorm hUnorm
  exact ⟨p, B, F, G, V, hpd, hBproj, hFproj, hGproj, hV⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension
