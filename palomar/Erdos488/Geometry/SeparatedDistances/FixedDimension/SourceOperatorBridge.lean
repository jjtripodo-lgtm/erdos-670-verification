module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceReserveBudgets
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.LiteralIncidence
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletedTrigonometricFeatures

@[expose] public section

/-! The source's actual three-group coefficient operator. This module starts
with the rational anchored potential and a whole-family matrix estimate. -/

open scoped BigOperators Matrix
open Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The rational vertex potential for the constant and second harmonic. -/
noncomputable def sourceQuadraticPotential {m : ℕ} (k : ℕ)
    (A B : Fin m) : ℝ :=
  if B.val < A.val then 64 / 9
  else if A.val < B.val then 9 * (k : ℝ) ^ 2 else 0

theorem sourceQuadraticPotential_self {m : ℕ} (k : ℕ) (A : Fin m) :
    sourceQuadraticPotential k A A = 0 := by
  simp [sourceQuadraticPotential]

theorem sourceQuadraticPotential_nonneg {m : ℕ} (k : ℕ) (A B : Fin m) :
    0 ≤ sourceQuadraticPotential k A B := by
  unfold sourceQuadraticPotential
  split_ifs <;> positivity

theorem sourceQuadraticPotential_le {m : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (A B : Fin m) :
    sourceQuadraticPotential k A B ≤ 9 * (k : ℝ) ^ 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold sourceQuadraticPotential
  split_ifs <;> nlinarith [sq_nonneg ((k : ℝ) - 1)]

/-- The scalar estimate used for every rational anchor potential. -/
theorem sourceQuadraticPotential_weighted_le {n : ℕ} (k : ℕ)
    (hk : 1 ≤ k) {K : ℝ} (hK : 0 < K) (A B : Fin (n+1)) :
    (sourceQuadraticPotential k A B / macroVertexWeight K B) ^ 2 ≤
      (9 * (k : ℝ) ^ 2 / K) ^ 2 := by
  have hq0 := sourceQuadraticPotential_nonneg k A B
  have hq := sourceQuadraticPotential_le k hk A B
  have hP := macroVertexWeight_ge_K K B
  have hPpos : 0 < macroVertexWeight K B := by linarith
  have hdiv : sourceQuadraticPotential k A B / macroVertexWeight K B ≤
      9 * (k : ℝ) ^ 2 / K := by
    apply (div_le_div_iff₀ hPpos hK).2
    calc
      sourceQuadraticPotential k A B * K ≤ 9 * (k : ℝ) ^ 2 * K :=
        mul_le_mul_of_nonneg_right hq (le_of_lt hK)
      _ ≤ 9 * (k : ℝ) ^ 2 * macroVertexWeight K B :=
        mul_le_mul_of_nonneg_left hP (by positivity)
  have hdiv0 : 0 ≤ sourceQuadraticPotential k A B / macroVertexWeight K B :=
    div_nonneg hq0 (le_of_lt hPpos)
  nlinarith [sq_nonneg (9 * (k : ℝ) ^ 2 / K)]

theorem sourceQuadraticPotential_energy_le {n : ℕ} (k : ℕ)
    (hk : 1 ≤ k) {K : ℝ} (hK : 0 < K) (A : Fin (n+1)) :
    16 * (∑ B : Fin (n+1),
      (sourceQuadraticPotential k A B / macroVertexWeight K B) ^ 2) ≤
      1296 * (n+1 : ℕ) * (k : ℝ) ^ 4 / K ^ 2 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun B (_ : B ∈ Finset.univ) =>
      sourceQuadraticPotential_weighted_le k hk hK A B)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hmul := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 16 by norm_num)
  calc
    _ ≤ 16 * ((n+1 : ℕ) * (9 * (k : ℝ) ^ 2 / K) ^ 2) := hmul
    _ = _ := by ring

/-- All rational quadratic coefficients can be chosen in the same macro
Euclidean space. The anchor solver is the one attached to a single physical
macro realization; no per-anchor change of centers occurs here. -/
theorem sourceQuadraticCoefficients_exist {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    {K : ℝ} (hK : 0 < K)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (hanchor : ∀ (A : Fin (n+1)) (z : Fin (n+1) → ℝ), z A = 0 →
      ∃ w : EuclideanSpace ℝ (Fin n),
        (∀ J, inner ℝ (p A-p J) w = z J) ∧
        ‖w‖ ^ 2 ≤ 16 * ∑ J,
          (z J / macroVertexWeight K J) ^ 2) :
    ∃ B : Fin (n+1) → EuclideanSpace ℝ (Fin n),
      (∀ A J, inner ℝ (p A-p J) (B A) =
        sourceQuadraticPotential k A J) ∧
      (∀ A, ‖B A‖ ^ 2 ≤
        1296 * (n+1 : ℕ) * (k : ℝ) ^ 4 / K ^ 2) := by
  have hsol : ∀ A : Fin (n+1), ∃ w : EuclideanSpace ℝ (Fin n),
      (∀ J, inner ℝ (p A-p J) w = sourceQuadraticPotential k A J) ∧
      ‖w‖ ^ 2 ≤ 16 * ∑ J,
        (sourceQuadraticPotential k A J / macroVertexWeight K J) ^ 2 := by
    intro A
    exact hanchor A (sourceQuadraticPotential k A)
      (sourceQuadraticPotential_self k A)
  choose B hproj henergy using hsol
  refine ⟨B, hproj, ?_⟩
  intro A
  exact (henergy A).trans (sourceQuadraticPotential_energy_le k hk hK A)

/-- The published constant/second-harmonic reserve is exactly three times
the sum of the individual rational coefficient-energy budgets. -/
theorem sourceReserve0Sq_eq_quadratic_operator_budget (m k : ℕ) :
    sourceReserve0Sq m k =
      3 * (m : ℝ) *
        (1296 * (m : ℝ) * (k : ℝ) ^ 4 / (sourceOffset m : ℝ) ^ 2) := by
  unfold sourceReserve0Sq
  ring

/-- A bound for entire linear combinations of columns, obtained by applying
finite Cauchy--Schwarz to every row and then summing rows. -/
theorem matrix_whole_family_bound_of_columns
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (b : ℝ)
    (hcol : ∀ a : κ, ∑ i : ι, (M i a) ^ 2 ≤ b) (x : κ → ℝ) :
    (∑ i : ι, (M *ᵥ x) i ^ 2) ≤
      (Fintype.card κ : ℝ) * b * ∑ a : κ, x a ^ 2 := by
  have hrow (i : ι) :
      (M *ᵥ x) i ^ 2 ≤
        (∑ a : κ, (M i a) ^ 2) * ∑ a : κ, x a ^ 2 := by
    simpa only [Matrix.mulVec, dotProduct] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a : κ => M i a) x)
  calc
    (∑ i : ι, (M *ᵥ x) i ^ 2) ≤
        ∑ i : ι, ((∑ a : κ, (M i a) ^ 2) * ∑ a : κ, x a ^ 2) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (∑ a : κ, ∑ i : ι, (M i a) ^ 2) * ∑ a : κ, x a ^ 2 := by
      rw [← Finset.sum_mul, Finset.sum_comm]
    _ ≤ ((∑ _a : κ, b) * ∑ a : κ, x a ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (Finset.sum_le_sum (fun a _ => hcol a))
        (Finset.sum_nonneg (fun a _ => sq_nonneg (x a)))
    _ = (Fintype.card κ : ℝ) * b * ∑ a : κ, x a ^ 2 := by simp

/-- Coordinate version of the preceding estimate for vectors in one fixed
Euclidean space. This is the needed whole-family estimate, not merely the
individual-vector energy bound. -/
theorem euclidean_whole_family_bound_of_vectors
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : κ → EuclideanSpace ℝ ι) (b : ℝ)
    (hB : ∀ a, ‖B a‖ ^ 2 ≤ b) (x : κ → ℝ) :
    (∑ i : ι, (∑ a : κ, x a * B a i) ^ 2) ≤
      (Fintype.card κ : ℝ) * b * ∑ a : κ, x a ^ 2 := by
  let M : Matrix ι κ ℝ := fun i a => B a i
  have hcol : ∀ a : κ, ∑ i : ι, (M i a) ^ 2 ≤ b := by
    intro a
    simpa only [M, EuclideanSpace.real_norm_sq_eq] using hB a
  simpa only [M, Matrix.mulVec, dotProduct, mul_comm] using
    matrix_whole_family_bound_of_columns M b hcol x

/-- The rational coefficient family consumes exactly the source's entire
constant/second-harmonic quadratic reserve, for every coefficient vector. -/
theorem sourceQuadraticCoefficients_whole_budget {n : ℕ} (k : ℕ)
    (hk : 1 ≤ k) (hK : 0 < (sourceOffset (n+1) : ℝ))
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (hanchor : ∀ (A : Fin (n+1)) (z : Fin (n+1) → ℝ), z A = 0 →
      ∃ w : EuclideanSpace ℝ (Fin n),
        (∀ J, inner ℝ (p A-p J) w = z J) ∧
        ‖w‖ ^ 2 ≤ 16 * ∑ J,
          (z J / macroVertexWeight (sourceOffset (n+1) : ℝ) J) ^ 2) :
    ∃ B : Fin (n+1) → EuclideanSpace ℝ (Fin n),
      (∀ A J, inner ℝ (p A-p J) (B A) =
        sourceQuadraticPotential k A J) ∧
      (∀ x : Fin (n+1) → ℝ,
        3 * (∑ i : Fin n, (∑ A : Fin (n+1), x A * B A i) ^ 2) ≤
          sourceReserve0Sq (n+1) k * ∑ A : Fin (n+1), x A ^ 2) := by
  obtain ⟨B, hproj, hB⟩ :=
    sourceQuadraticCoefficients_exist k hk hK p hanchor
  refine ⟨B, hproj, ?_⟩
  intro x
  have hwhole := euclidean_whole_family_bound_of_vectors B
    (1296 * (n+1 : ℕ) * (k : ℝ) ^ 4 /
      (sourceOffset (n+1) : ℝ) ^ 2) hB x
  have hscaled := mul_le_mul_of_nonneg_left hwhole
    (show (0 : ℝ) ≤ 3 by norm_num)
  rw [sourceReserve0Sq_eq_quadratic_operator_budget]
  simpa only [Fintype.card_fin, mul_assoc] using hscaled

/-- Both literal incidence families are solved in the very same physical
macro realization, with the *whole-family* fine/coarse operator estimates.
The anchor-column shifts are handled separately. -/
theorem sourceFineCoarseCoefficients_exist {n : ℕ} (hn : 1 ≤ n)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 16384 * (harmonic (n+2) : ℝ) ^ 2 ≤ K)
    (r : ℝ) (hr : r ≤ K ^ 2 / 16)
    (hnK : (n+1 : ℕ) ≤ K)
    (p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hpd : ∀ i j,
      ‖p j-p i‖ ^ 2 =
        offDiagonalShift (colexSqData (m:=n+1) K) r i j) :
    ∃ F G : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)),
      (∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
        fineIncidence (n+1) K i a) ∧
      (∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
        coarseIncidence (n+1) K i a) ∧
      (∀ t : Fin (n+1) → ℝ,
        ‖∑ a, t a • F a‖ ^ 2 ≤
          576 * (K+(n+1 : ℕ)) * ∑ a, t a ^ 2) ∧
      (∀ t : Fin (n+1) → ℝ,
        ‖∑ a, t a • G a‖ ^ 2 ≤
          3600 * (K+(n+1 : ℕ)) * ∑ a, t a ^ 2) := by
  obtain ⟨F, hFproj, hFenergy⟩ :=
    whole_solve_in_flattened_realization hn hK hlarge r hr p hpd
      (fineIncidence (n+1) K)
  obtain ⟨G, hGproj, hGenergy⟩ :=
    whole_solve_in_flattened_realization hn hK hlarge r hr p hpd
      (coarseIncidence (n+1) K)
  refine ⟨F, G, hFproj, hGproj, ?_, ?_⟩
  · intro t
    have hbound := (literal_fine_coarse_incidence_bounds
      (by linarith : 0 < K) hnK t).1
    have hfactor : 0 ≤ 144 * (K+(n+1 : ℕ)) := by positivity
    calc
      _ ≤ 144 * (K+(n+1 : ℕ)) *
            ∑ i, ((fineIncidence (n+1) K *ᵥ t) i /
              colexANat K (i.val+1)) ^ 2 := hFenergy t
      _ ≤ 144 * (K+(n+1 : ℕ)) * (4 * ∑ a, t a ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hfactor
      _ = _ := by ring

  · intro t
    have hbound := (literal_fine_coarse_incidence_bounds
      (by linarith : 0 < K) hnK t).2
    have hfactor : 0 ≤ 144 * (K+(n+1 : ℕ)) := by positivity
    calc
      _ ≤ 144 * (K+(n+1 : ℕ)) *
            ∑ i, ((coarseIncidence (n+1) K *ᵥ t) i /
              colexANat K (i.val+1)) ^ 2 := hGenergy t
      _ ≤ 144 * (K+(n+1 : ℕ)) * (25 * ∑ a, t a ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hfactor
      _ = _ := by ring

/-- Incidence projection equations telescope with the sign convention of the
actual macro increments. -/
theorem anchored_projection_of_pathIncidence
    {n : ℕ} (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) (z : Fin (n+1) → ℝ)
    (A : Fin (n+1)) (hA : z A = 0)
    (hedge : ∀ i : Fin n,
      inner ℝ (p i.succ-p i.castSucc) w =
        (pathIncidence n *ᵥ z) i) (J : Fin (n+1)) :
    inner ℝ (p A-p J) w = z J := by
  have hedges : ∀ i : Fin n,
      inner ℝ (p i.succ) w-inner ℝ (p i.castSucc) w =
        z i.castSucc-z i.succ := by
    intro i
    simpa only [inner_sub_left, pathIncidence_mulVec_eq] using hedge i
  have ha := consecutive_potential_constant
    (fun V => inner ℝ (p V) w) z hedges A
  have hj := consecutive_potential_constant
    (fun V => inner ℝ (p V) w) z hedges J
  rw [hA] at ha
  rw [inner_sub_left]
  linarith

theorem sourceFineCoefficient_anchor_projection {n : ℕ} (K : ℝ)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence n K i a) (a : Fin n) (J : Fin (n+1)) :
    inner ℝ (p a.succ-p J) (F a) = finePotential K a J := by
  apply anchored_projection_of_pathIncidence p (F a)
    (finePotential K a) a.succ
  · simp [finePotential]
  · intro i
    exact hF i a

theorem sourceCoarseCoefficient_anchor_projection {n : ℕ} (K : ℝ)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (G : Fin n → EuclideanSpace ℝ (Fin n))
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence n K i a) (a : Fin n) (J : Fin (n+1)) :
    inner ℝ (p a.castSucc-p J) (G a) = coarsePotential K a J := by
  apply anchored_projection_of_pathIncidence p (G a)
    (coarsePotential K a) a.castSucc
  · simp [coarsePotential]
  · intro i
    exact hG i a

/-- The fine source potential is exactly the colex distance to an earlier
vertex; its anchor is `a+1`. -/
theorem finePotential_eq_colex {n : ℕ} (K : ℝ)
    (a : Fin n) (J : Fin (n+1)) :
    finePotential K a J =
      if J.val < a.succ.val then colexDistance K a.succ J else 0 := by
  by_cases h : J.val < a.val+1
  · have hnot : ¬a.val+1 < J.val := by omega
    simp [finePotential, colexDistance, h, hnot, colexLabel]
    ring
  · simp [finePotential, h]

/-- The coarse source potential is exactly the colex distance to a later
vertex; its anchor is `a`. -/
theorem coarsePotential_eq_colex {n : ℕ} (K : ℝ)
    (a : Fin n) (J : Fin (n+1)) :
    coarsePotential K a J =
      if a.castSucc.val < J.val then colexDistance K a.castSucc J else 0 := by
  by_cases h : a.val < J.val
  · simp [coarsePotential, colexDistance, h, colexLabel]
    ring
  · simp [coarsePotential, h]

/-- Fine column `a` belongs to macro anchor `a+1`; anchor zero has no fine
column. -/
def sourceFineShift {n : ℕ} {E : Type*} [Zero E]
    (F : Fin n → E) : Fin (n+1) → E := Fin.cases 0 F

/-- Coarse column `a` belongs to macro anchor `a`; the final anchor has no
coarse column. -/
def sourceCoarseShift {n : ℕ} {E : Type*} [Zero E]
    (G : Fin n → E) : Fin (n+1) → E := Fin.snoc G 0

theorem sourceFineShift_anchor_projection {n : ℕ} (K : ℝ)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence n K i a) (A J : Fin (n+1)) :
    inner ℝ (p A-p J) (sourceFineShift F A) =
      if J.val < A.val then colexDistance K A J else 0 := by
  cases A using Fin.cases with
  | zero => simp [sourceFineShift]
  | succ a =>
      simpa only [sourceFineShift, Fin.cases_succ] using
        (sourceFineCoefficient_anchor_projection K p F hF a J).trans
          (finePotential_eq_colex K a J)

theorem sourceCoarseShift_anchor_projection {n : ℕ} (K : ℝ)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (G : Fin n → EuclideanSpace ℝ (Fin n))
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence n K i a) (A J : Fin (n+1)) :
    inner ℝ (p A-p J) (sourceCoarseShift G A) =
      if A.val < J.val then colexDistance K A J else 0 := by
  cases A using Fin.lastCases with
  | last =>
      have h : ¬ n < J.val := by omega
      simp [sourceCoarseShift, h]
  | cast a =>
      simpa only [sourceCoarseShift, Fin.snoc_castSucc] using
        (sourceCoarseCoefficient_anchor_projection K p G hG a J).trans
          (coarsePotential_eq_colex K a J)

theorem sourceFineShift_sum {n : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (F : Fin n → E)
    (t : Fin (n+1) → ℝ) :
    (∑ A : Fin (n+1), t A • sourceFineShift F A) =
      ∑ a : Fin n, t a.succ • F a := by
  rw [Fin.sum_univ_succ]
  simp [sourceFineShift]

theorem sourceCoarseShift_sum {n : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (G : Fin n → E)
    (t : Fin (n+1) → ℝ) :
    (∑ A : Fin (n+1), t A • sourceCoarseShift G A) =
      ∑ a : Fin n, t a.castSucc • G a := by
  rw [Fin.sum_univ_castSucc]
  simp [sourceCoarseShift]

theorem sourceFineShift_sq_sum_le {n : ℕ} (t : Fin (n+1) → ℝ) :
    (∑ a : Fin n, t a.succ ^ 2) ≤ ∑ A : Fin (n+1), t A ^ 2 := by
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg (t 0))

theorem sourceCoarseShift_sq_sum_le {n : ℕ} (t : Fin (n+1) → ℝ) :
    (∑ a : Fin n, t a.castSucc ^ 2) ≤ ∑ A : Fin (n+1), t A ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (sq_nonneg (t (Fin.last n)))

theorem sourceFineShift_whole_bound {n : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (F : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • F a‖ ^ 2 ≤
        576 * (K+(n : ℕ)) * ∑ a, t a ^ 2)
    (t : Fin (n+1) → ℝ) :
    ‖∑ A, t A • sourceFineShift F A‖ ^ 2 ≤
      576 * (K+(n : ℕ)) * ∑ A, t A ^ 2 := by
  rw [sourceFineShift_sum]
  calc
    _ ≤ 576 * (K+(n : ℕ)) * ∑ a : Fin n, t a.succ ^ 2 :=
      hF (fun a => t a.succ)
    _ ≤ 576 * (K+(n : ℕ)) * ∑ A : Fin (n+1), t A ^ 2 :=
      mul_le_mul_of_nonneg_left (sourceFineShift_sq_sum_le t) (by positivity)

theorem sourceCoarseShift_whole_bound {n : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (G : Fin n → EuclideanSpace ℝ (Fin n))
    (hG : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • G a‖ ^ 2 ≤
        3600 * (K+(n : ℕ)) * ∑ a, t a ^ 2)
    (t : Fin (n+1) → ℝ) :
    ‖∑ A, t A • sourceCoarseShift G A‖ ^ 2 ≤
      3600 * (K+(n : ℕ)) * ∑ A, t A ^ 2 := by
  rw [sourceCoarseShift_sum]
  calc
    _ ≤ 3600 * (K+(n : ℕ)) * ∑ a : Fin n, t a.castSucc ^ 2 :=
      hG (fun a => t a.castSucc)
    _ ≤ 3600 * (K+(n : ℕ)) * ∑ A : Fin (n+1), t A ^ 2 :=
      mul_le_mul_of_nonneg_left (sourceCoarseShift_sq_sum_le t) (by positivity)

/-- The sharp whole-family triangle estimate behind the source's 84 constant.
Applying a factor-two square estimate here would exceed the source reserve. -/
theorem source_sharp_sine_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X Y : E) (W S c : ℝ)
    (hW : 0 ≤ W) (hS : 0 ≤ S) (hc : 1 ≤ c)
    (hX : ‖X‖ ^ 2 ≤ 576 * W * S)
    (hY : ‖Y‖ ^ 2 ≤ 3600 * W * S) :
    ‖X+c • Y‖ ^ 2 ≤ 7056 * c ^ 2 * W * S := by
  let T := Real.sqrt (W*S)
  have hWS : 0 ≤ W*S := mul_nonneg hW hS
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hT2 : T^2 = W*S := Real.sq_sqrt hWS
  have hX' : ‖X‖ ≤ 24*T := by
    have hn := norm_nonneg X
    nlinarith [hX]
  have hY' : ‖Y‖ ≤ 60*T := by
    have hn := norm_nonneg Y
    nlinarith [hY]
  have hc0 : 0 ≤ c := by linarith
  have htri : ‖X+c • Y‖ ≤ ‖X‖+c*‖Y‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0] using
      (norm_add_le X (c • Y))
  have hYmul := mul_le_mul_of_nonneg_left hY' hc0
  have hnorm : ‖X+c • Y‖ ≤ 84*c*T := by
    have h84 : (24+60*c)*T ≤ 84*c*T := by nlinarith
    linarith
  have hnonneg : 0 ≤ ‖X+c • Y‖ := norm_nonneg _
  nlinarith [sq_nonneg (84*c*T-‖X+c • Y‖)]

/-- After the two endpoint shifts, the literal fine/coarse columns obey the
sharp 84-constant whole-family bound. -/
theorem source_shifted_sine_whole_bound {n : ℕ} {K c : ℝ}
    (hK : 0 ≤ K) (hc : 1 ≤ c)
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • F a‖ ^ 2 ≤
        576 * (K+(n : ℕ)) * ∑ a, t a ^ 2)
    (hG : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • G a‖ ^ 2 ≤
        3600 * (K+(n : ℕ)) * ∑ a, t a ^ 2)
    (t : Fin (n+1) → ℝ) :
    ‖∑ A, t A • (sourceFineShift F A + c • sourceCoarseShift G A)‖ ^ 2 ≤
      7056 * c ^ 2 * (K+(n : ℕ)) * ∑ A, t A ^ 2 := by
  let X := ∑ A, t A • sourceFineShift F A
  let Y := ∑ A, t A • sourceCoarseShift G A
  have hsum :
      (∑ A, t A • (sourceFineShift F A + c • sourceCoarseShift G A)) =
        X+c • Y := by
    simp [X, Y, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
      mul_comm]
  rw [hsum]
  apply source_sharp_sine_triangle X Y (K+(n : ℕ))
    (∑ A, t A ^ 2) c (by positivity)
    (Finset.sum_nonneg (fun A _ => sq_nonneg _)) hc
  · exact sourceFineShift_whole_bound hK F hF t
  · exact sourceCoarseShift_whole_bound hK G hG t

/-- The actual first-harmonic macro coefficient at each anchor. -/
noncomputable def sourceSineCoefficient {n : ℕ} (k : ℕ)
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (A : Fin (n+1)) : EuclideanSpace ℝ (Fin n) :=
  ((9/8 : ℝ) / sourceTheta k) •
    (sourceFineShift F A + ((9/8 : ℝ) * (k : ℝ)) • sourceCoarseShift G A)

/-- The directed scalar attached to an anchor and a distinct target. -/
noncomputable def sourceDirectedScale {n : ℕ} (k : ℕ)
    (A J : Fin n) : ℝ :=
  if A.val < J.val then (9/8 : ℝ) * (k : ℝ) else 1

theorem sourceSineCoefficient_anchor_projection {n : ℕ} (K : ℝ) (k : ℕ)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence n K i a)
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence n K i a)
    (A J : Fin (n+1)) (hAJ : A ≠ J) :
    inner ℝ (p A-p J) (sourceSineCoefficient k F G A) =
      ((9/8 : ℝ) / sourceTheta k) *
        sourceDirectedScale k A J * colexDistance K A J := by
  rw [sourceSineCoefficient, real_inner_smul_right, inner_add_right,
    real_inner_smul_right]
  rw [sourceFineShift_anchor_projection K p F hF A J,
    sourceCoarseShift_anchor_projection K p G hG A J]
  by_cases hlt : A.val < J.val
  · have hnot : ¬J.val < A.val := by omega
    simp [sourceDirectedScale, hlt, hnot]
    ring
  · have hgt : J.val < A.val := by
      have hne : A.val ≠ J.val := fun h => hAJ (Fin.ext h)
      omega
    simp [sourceDirectedScale, hlt, hgt]

/-- The source first-harmonic reserve pays for the *entire* shifted sine
family. The proof retains the sharp 84 constant. -/
theorem sourceSineCoefficients_whole_budget {n : ℕ} (k : ℕ)
    (hm : 34000 ≤ n+1) (hk : 2 ≤ k)
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • F a‖ ^ 2 ≤
        576 * ((sourceOffset (n+1) : ℝ)+(n : ℕ)) * ∑ a, t a ^ 2)
    (hG : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • G a‖ ^ 2 ≤
        3600 * ((sourceOffset (n+1) : ℝ)+(n : ℕ)) * ∑ a, t a ^ 2)
    (t : Fin (n+1) → ℝ) :
    3 * ‖∑ A, t A • sourceSineCoefficient k F G A‖ ^ 2 ≤
      sourceReserve1Sq (n+1) k * ∑ A, t A ^ 2 := by
  let K : ℝ := sourceOffset (n+1)
  let c : ℝ := (9/8 : ℝ) * (k : ℝ)
  let s : ℝ := (9/8 : ℝ) / sourceTheta k
  let W : ℝ := K+(n+1 : ℕ)
  let S : ℝ := ∑ A : Fin (n+1), t A ^ 2
  have hc : 1 ≤ c := by
    dsimp [c]
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith only [hk']
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun A _ => sq_nonneg _)
  have hθ : 0 < sourceTheta k := sourceTheta_pos k (by omega)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsum : (∑ A, t A • sourceSineCoefficient k F G A) =
      s • (∑ A, t A •
        (sourceFineShift F A+c • sourceCoarseShift G A)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro A _
    change t A • (s • (sourceFineShift F A+c • sourceCoarseShift G A)) =
      s • (t A • (sourceFineShift F A+c • sourceCoarseShift G A))
    exact smul_comm _ _ _
  have hsharp := source_shifted_sine_whole_bound hK hc F G hF hG t
  have hW0 : K+(n : ℕ) ≤ W := by
    dsimp [W]
    push_cast
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hsharp
    (show 0 ≤ 3*s^2 by positivity)
  have hWscaled := mul_le_mul_of_nonneg_left hW0
    (show 0 ≤ 3*s^2*7056*c^2*S by positivity)
  have hformula : sourceReserve1Sq (n+1) k * S =
      3*s^2*(7056*c^2*W*S) := by
    rw [sourceReserve1Sq_eq_operator_formula (n+1) k hm hk]
    dsimp [s, c, W, K]
    simp only [mul_pow, div_pow, Real.sq_sqrt (by positivity :
      0 ≤ (sourceOffset (n+1) : ℝ)+(n+1 : ℕ))]
    ring
  rw [hsum]
  calc
    3 * ‖s • (∑ A, t A •
        (sourceFineShift F A+c • sourceCoarseShift G A))‖ ^ 2 =
      3*s^2*‖∑ A, t A •
        (sourceFineShift F A+c • sourceCoarseShift G A)‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
        ring
    _ ≤ 3*s^2*(7056*c^2*(K+(n : ℕ))*S) := hscaled
    _ = (3*s^2*7056*c^2*S)*(K+(n : ℕ)) := by ring
    _ ≤ (3*s^2*7056*c^2*S)*W := hWscaled
    _ = sourceReserve1Sq (n+1) k * S := by rw [hformula]; ring

/-- Coordinates of a linear combination in the fixed macro Euclidean space. -/
theorem euclidean_sum_norm_sq_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : κ → EuclideanSpace ℝ ι) (t : κ → ℝ) :
    ‖∑ a, t a • B a‖ ^ 2 =
      ∑ i : ι, (∑ a, t a * B a i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  ext i
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- One coefficient family placed in one of the five source feature slots. -/
noncomputable def sourceSlotMatrix {ι κ : Type*}
    (B : κ → EuclideanSpace ℝ ι) (slot : Fin 5) :
    Matrix ι (κ × Fin 5) ℝ :=
  fun i q => if q.2 = slot then B q.1 i else 0

theorem sourceSlotMatrix_mulVec {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (B : κ → EuclideanSpace ℝ ι) (slot : Fin 5)
    (x : κ × Fin 5 → ℝ) (i : ι) :
    (sourceSlotMatrix B slot *ᵥ x) i =
      ∑ a : κ, x (a,slot) * B a i := by
  simp [sourceSlotMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, mul_comm]

theorem sourceSlotMatrix_clusteredFeature {ι : Type*} [Fintype ι]
    {m : ℕ} (B : Fin m → EuclideanSpace ℝ ι)
    (slot : Fin 5) (A : Fin m) (z : ℝ) (i : ι) :
    (sourceSlotMatrix B slot *ᵥ clusteredFeature A z) i =
      B A i * trigFeature z slot := by
  rw [sourceSlotMatrix_mulVec]
  simp [clusteredFeature]
  ring

theorem sourceSlotMatrix_energy {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (B : κ → EuclideanSpace ℝ ι) (slot : Fin 5)
    (b : ℝ)
    (hB : ∀ t : κ → ℝ,
      3 * (∑ i : ι, (∑ a : κ, t a * B a i) ^ 2) ≤
        b ^ 2 * ∑ a : κ, t a ^ 2)
    (x : κ × Fin 5 → ℝ) :
    3 * (∑ i : ι, (sourceSlotMatrix B slot *ᵥ x) i ^ 2) ≤
      b ^ 2 * ∑ a : κ, x (a,slot) ^ 2 := by
  simpa only [sourceSlotMatrix_mulVec] using hB (fun a => x (a,slot))

/-- Inactive feature slots only add nonnegative diagonal reserve. -/
theorem source_three_active_slots_le_diagonal {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (b₀ b₁ : ℝ) (x : κ × Fin 5 → ℝ) :
    b₀ ^ 2 * (∑ a : κ, x (a,0) ^ 2) +
      b₁ ^ 2 * (∑ a : κ, x (a,1) ^ 2) +
      b₀ ^ 2 * (∑ a : κ, x (a,4) ^ 2) ≤
        x ⬝ᵥ (Matrix.diagonal
          (fun q : κ × Fin 5 => trigWeight b₀ b₁ b₀ q.2) *ᵥ x) := by
  have hpoint (a : κ) :
      b₀ ^ 2 * x (a,0) ^ 2 +
        b₁ ^ 2 * x (a,1) ^ 2 +
        b₀ ^ 2 * x (a,4) ^ 2 ≤
          ∑ s : Fin 5, trigWeight b₀ b₁ b₀ s * x (a,s) ^ 2 := by
    simp [Fin.sum_univ_succ, trigWeight]
    have h₂ : 0 ≤ b₁ ^ 2 * x (a,2) ^ 2 := by positivity
    have h₃ : 0 ≤ b₀ ^ 2 * x (a,3) ^ 2 := by positivity
    linarith
  rw [diagonal_bilinear_sum]
  rw [Fintype.sum_prod_type]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simpa only [Finset.sum_add_distrib, Finset.mul_sum, pow_two,
    mul_assoc] using h

/-- The actual three occupied feature slots, once their whole-family budgets
are known, admit a residual factor on the same finite feature index type. -/
theorem source_three_group_completion_factor {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B U : κ → EuclideanSpace ℝ ι) (b₀ b₁ : ℝ)
    (hB : ∀ t : κ → ℝ,
      3 * ‖∑ a, t a • B a‖ ^ 2 ≤ b₀ ^ 2 * ∑ a, t a ^ 2)
    (hU : ∀ t : κ → ℝ,
      3 * ‖∑ a, t a • U a‖ ^ 2 ≤ b₁ ^ 2 * ∑ a, t a ^ 2) :
    ∃ V : Matrix (κ × Fin 5) (κ × Fin 5) ℝ,
      (sourceSlotMatrix B 0 + sourceSlotMatrix U 1 +
        sourceSlotMatrix (fun a => -B a) 4)ᵀ *
      (sourceSlotMatrix B 0 + sourceSlotMatrix U 1 +
        sourceSlotMatrix (fun a => -B a) 4) + Vᵀ * V =
        Matrix.diagonal (fun q : κ × Fin 5 => trigWeight b₀ b₁ b₀ q.2) := by
  let A₀ := sourceSlotMatrix B 0
  let A₁ := sourceSlotMatrix U 1
  let A₄ := sourceSlotMatrix (fun a => -B a) 4
  have hBcoord (t : κ → ℝ) :
      3 * (∑ i : ι, (∑ a : κ, t a * B a i) ^ 2) ≤
        b₀ ^ 2 * ∑ a, t a ^ 2 := by
    simpa only [euclidean_sum_norm_sq_eq] using hB t
  have hUcoord (t : κ → ℝ) :
      3 * (∑ i : ι, (∑ a : κ, t a * U a i) ^ 2) ≤
        b₁ ^ 2 * ∑ a, t a ^ 2 := by
    simpa only [euclidean_sum_norm_sq_eq] using hU t
  have hCnorm (t : κ → ℝ) :
      3 * ‖∑ a, t a • (-B a)‖ ^ 2 ≤
        b₀ ^ 2 * ∑ a, t a ^ 2 := by
    simpa only [smul_neg, Finset.sum_neg_distrib, norm_neg] using hB t
  have hCcoord (t : κ → ℝ) :
      3 * (∑ i : ι, (∑ a : κ, t a * (-B a) i) ^ 2) ≤
        b₀ ^ 2 * ∑ a, t a ^ 2 := by
    simpa only [euclidean_sum_norm_sq_eq] using hCnorm t
  have hbudget (x : κ × Fin 5 → ℝ) :
      3 * ∑ i, (A₀ *ᵥ x) i ^ 2 +
      3 * ∑ i, (A₁ *ᵥ x) i ^ 2 +
      3 * ∑ i, (A₄ *ᵥ x) i ^ 2 ≤
        x ⬝ᵥ (Matrix.diagonal
          (fun q : κ × Fin 5 => trigWeight b₀ b₁ b₀ q.2) *ᵥ x) := by
    have h₀ := sourceSlotMatrix_energy B 0 b₀ hBcoord x
    have h₁ := sourceSlotMatrix_energy U 1 b₁ hUcoord x
    have h₄ := sourceSlotMatrix_energy (fun a => -B a) 4 b₀ hCcoord x
    have hdiag := source_three_active_slots_le_diagonal b₀ b₁ x
    dsimp [A₀, A₁, A₄]
    linarith
  obtain ⟨V, hV⟩ := three_group_completion_factor A₀ A₁ A₄
    (Matrix.diagonal (fun q : κ × Fin 5 => trigWeight b₀ b₁ b₀ q.2))
    (Matrix.isHermitian_diagonal _) hbudget
  exact ⟨V, hV⟩

/-- The literal three-active-slot coefficient operator of the source
construction. Slots two and three are zero. -/
noncomputable def sourceActiveMatrix {n : ℕ} (k : ℕ)
    (B : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin (n+1) × Fin 5) ℝ :=
  sourceSlotMatrix B 0 + sourceSlotMatrix (sourceSineCoefficient k F G) 1 +
    sourceSlotMatrix (fun a => -B a) 4

theorem sourceActiveMatrix_feature_apply {n : ℕ} (k : ℕ)
    (B : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (A : Fin (n+1)) (z : ℝ) (i : Fin n) :
    (sourceActiveMatrix k B F G *ᵥ clusteredFeature A z) i =
      B A i * (1-Real.cos (2*z)) +
        sourceSineCoefficient k F G A i * Real.sin z := by
  simp [sourceActiveMatrix, Matrix.add_mulVec,
    sourceSlotMatrix_clusteredFeature, trigFeature]
  ring

theorem euclidean_dot_inner {ι : Type*} [Fintype ι]
    (v w : EuclideanSpace ℝ ι) :
    (fun i => v i) ⬝ᵥ (fun i => w i) = inner ℝ v w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- Literal source feature projection in one actual macro realization.
The rational potential supplies the second-harmonic term and the shifted
incidence operator supplies the first-harmonic term. -/
theorem sourceActiveMatrix_anchor_projection {n : ℕ} (K : ℝ) (k : ℕ)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (B : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hB : ∀ A J, inner ℝ (p A-p J) (B A) =
      sourceQuadraticPotential k A J)
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence n K i a)
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence n K i a)
    (A J : Fin (n+1)) (hAJ : A ≠ J) (z : ℝ) :
    (fun i => (p A-p J) i) ⬝ᵥ
      (sourceActiveMatrix k B F G *ᵥ clusteredFeature A z) =
      sourceQuadraticPotential k A J * (1-Real.cos (2*z)) +
        ((9/8 : ℝ) / sourceTheta k) *
          sourceDirectedScale k A J * colexDistance K A J * Real.sin z := by
  have hdotB : (∑ i : Fin n, (p A-p J) i * B A i) =
      inner ℝ (p A-p J) (B A) := euclidean_dot_inner _ _
  have hdotU : (∑ i : Fin n,
      (p A-p J) i * sourceSineCoefficient k F G A i) =
      inner ℝ (p A-p J) (sourceSineCoefficient k F G A) :=
    euclidean_dot_inner _ _
  calc
    _ = (∑ i : Fin n, (p A-p J) i * B A i) *
          (1-Real.cos (2*z)) +
        (∑ i : Fin n,
          (p A-p J) i * sourceSineCoefficient k F G A i) * Real.sin z := by
      simp only [dotProduct, sourceActiveMatrix_feature_apply,
        mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ = _ := by
      rw [hdotB, hdotU, hB A J,
        sourceSineCoefficient_anchor_projection K k p F G hF hG A J hAJ]

/-- The rational potential has exactly the source's quadratic cross
coefficient, in either anchor direction. -/
theorem sourceQuadraticPotential_metric_identity {m : ℕ} (k : ℕ)
    (hk : 0 < k) (A J : Fin m) (hAJ : A ≠ J) :
    4 * sourceMacroStep (k : ℝ) * sourceQuadraticPotential k A J *
      (sourceTheta k)^2 =
        ((9/8 : ℝ) * sourceDirectedScale k A J)^2 := by
  have hscale := source_theta_scale k hk
  change (sourceTheta k)^2 * (k : ℝ)^2 = 1/32 at hscale
  by_cases hlt : A.val < J.val
  · have hnot : ¬ J.val < A.val := by omega
    simp only [sourceQuadraticPotential, if_neg hnot, if_pos hlt,
      sourceDirectedScale]
    unfold sourceMacroStep
    nlinarith [hscale]
  · have hgt : J.val < A.val := by
      have hne : A.val ≠ J.val := fun h => hAJ (Fin.ext h)
      omega
    simp only [sourceQuadraticPotential, if_pos hgt, sourceDirectedScale,
      if_neg hlt]
    unfold sourceMacroStep
    nlinarith [hscale]

/-- Both literal directed projections have the source's exact linear and
quadratic digit terms. This is the algebraic input to the actual Euclidean
cross-metric identity. -/
theorem sourceActiveMatrix_projection_metric {n : ℕ} (K : ℝ) (k : ℕ)
    (hk : 0 < k)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (B : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hB : ∀ A J, inner ℝ (p A-p J) (B A) =
      sourceQuadraticPotential k A J)
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence n K i a)
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence n K i a)
    (A J : Fin (n+1)) (hAJ : A ≠ J) (z : ℝ) :
    let α := ((9/8 : ℝ) * sourceDirectedScale k A J) *
      Real.sin z / sourceTheta k
    2 * sourceMacroStep (k : ℝ) *
      ((fun i => (p A-p J) i) ⬝ᵥ
        (sourceActiveMatrix k B F G *ᵥ clusteredFeature A z)) =
      2 * (sourceMacroStep (k : ℝ) * colexDistance K A J) * α + α^2 := by
  rw [sourceActiveMatrix_anchor_projection K k p B F G hB hF hG A J hAJ z]
  dsimp
  rw [Real.cos_two_mul_eq_one_sub]
  have hθ : sourceTheta k ≠ 0 := (sourceTheta_pos k hk).ne'
  have hq := sourceQuadraticPotential_metric_identity k hk A J hAJ
  field_simp
  nlinarith [hq]

theorem sourceActiveMatrix_forward_projection_metric {n : ℕ} (K : ℝ) (k : ℕ)
    (hk : 0 < k)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (B : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hB : ∀ A J, inner ℝ (p A-p J) (B A) =
      sourceQuadraticPotential k A J)
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence n K i a)
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence n K i a)
    (A J : Fin (n+1)) (hAJ : A.val < J.val) (i : ℕ) :
    2 * sourceMacroStep (k : ℝ) *
      ((fun a => (p A-p J) a) ⬝ᵥ
        (sourceActiveMatrix k B F G *ᵥ clusteredFeature A
          (sourceTheta k * ((i : ℝ)-((k : ℝ)-1)/2)))) =
      2 * (sourceMacroStep (k : ℝ) * colexDistance K A J) *
        sourceAlpha k i + (sourceAlpha k i)^2 := by
  have h := sourceActiveMatrix_projection_metric K k hk p B F G
    hB hF hG A J (Fin.ne_of_lt hAJ)
    (sourceTheta k * ((i : ℝ)-((k : ℝ)-1)/2))
  simp [sourceAlpha, sourceDigit, sineDigit, sourceTheta,
    sourceDirectedScale, hAJ] at h ⊢
  convert h using 1; ring

theorem sourceActiveMatrix_reverse_projection_metric {n : ℕ} (K : ℝ) (k : ℕ)
    (hk : 0 < k)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (B : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hB : ∀ A J, inner ℝ (p A-p J) (B A) =
      sourceQuadraticPotential k A J)
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
      fineIncidence n K i a)
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
      coarseIncidence n K i a)
    (A J : Fin (n+1)) (hJA : J.val < A.val) (i : ℕ) :
    2 * sourceMacroStep (k : ℝ) *
      ((fun a => (p A-p J) a) ⬝ᵥ
        (sourceActiveMatrix k B F G *ᵥ clusteredFeature A
          (sourceTheta k * ((i : ℝ)-((k : ℝ)-1)/2)))) =
      2 * (sourceMacroStep (k : ℝ) * colexDistance K A J) *
        sourceBeta k i + (sourceBeta k i)^2 := by
  have h := sourceActiveMatrix_projection_metric K k hk p B F G
    hB hF hG A J (Fin.ne_of_gt hJA)
    (sourceTheta k * ((i : ℝ)-((k : ℝ)-1)/2))
  have hnot : ¬ A.val < J.val := by omega
  simp [sourceBeta, sourceDigit, sineDigit, sourceTheta,
    sourceDirectedScale, hnot] at h ⊢
  convert h using 1; ring

/-- One source macro realization carries every rational and incidence
coefficient, and its complete three-group operator budget has a residual Gram
factor without adding any feature coordinates. Scalar source offset/radius
hypotheses are explicit; this is not the unconditional #670 theorem. -/
theorem source_actual_operator_completion {n k : ℕ}
    (hn : 1 ≤ n) (hm : 34000 ≤ n+2) (hk : 2 ≤ k)
    (hK : 10 ≤ (sourceOffset (n+2) : ℝ))
    (hlarge : 16384 * (harmonic (n+2) : ℝ) ^ 2 ≤
      (sourceOffset (n+2) : ℝ))
    (r : ℝ) (hr : r ≤ (sourceOffset (n+2) : ℝ) ^ 2 / 16)
    (hnK : (n+1 : ℕ) ≤ (sourceOffset (n+2) : ℝ)) :
    ∃ p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ B : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ F G : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ V : Matrix (Fin (n+2) × Fin 5) (Fin (n+2) × Fin 5) ℝ,
      (∀ i j, ‖p j-p i‖ ^ 2 =
        offDiagonalShift (colexSqData (m:=n+1)
          (sourceOffset (n+2) : ℝ)) r i j) ∧
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
  obtain ⟨p, _, hpd, hanchor⟩ :=
    flattened_colex_all_anchor_potentials hn hK hlarge r hr
  obtain ⟨B, hBproj, hBbudget⟩ :=
    sourceQuadraticCoefficients_whole_budget k (by omega)
      (by linarith : 0 < (sourceOffset (n+2) : ℝ)) p hanchor
  obtain ⟨F, G, hFproj, hGproj, hFbudget, hGbudget⟩ :=
    sourceFineCoarseCoefficients_exist hn hK hlarge r hr hnK p hpd
  have hBnorm (t : Fin (n+2) → ℝ) :
      3 * ‖∑ A, t A • B A‖ ^ 2 ≤
        (sourceReserve0 (n+2) k) ^ 2 * ∑ A, t A ^ 2 := by
    rw [euclidean_sum_norm_sq_eq, sourceReserve0_square]
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
