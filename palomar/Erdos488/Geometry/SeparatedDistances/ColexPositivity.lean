module

public import Erdos488.Geometry.SeparatedDistances.GramRealization
public import Erdos488.Geometry.SeparatedDistances.EuclideanRealization
public import Erdos488.Geometry.SeparatedDistances.Labels
public import Erdos488.Geometry.SeparatedDistances.ColexBase
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators
open Matrix

/-- The symmetric pure-colex prescribed distance on `m+1` vertices. -/
def colexDistance {m : ℕ} (K : ℝ) (i j : Fin (m + 1)) : ℝ :=
  if i.val < j.val then K + colexLabel i.val j.val
  else if j.val < i.val then K + colexLabel j.val i.val
  else 0

/-- Squared pure-colex distance data. -/
def colexSqData {m : ℕ} (K : ℝ) : SqDistanceData (Fin (m + 1)) :=
  fun i j => colexDistance K i j ^ 2

/-- The prescribed distance from a vertex to itself vanishes. -/
@[simp] theorem colexDistance_self {m : ℕ} (K : ℝ) (i : Fin (m + 1)) :
    colexDistance K i i = 0 := by
  simp [colexDistance]

/-- Pure-colex prescribed distances are symmetric. -/
theorem colexDistance_symm {m : ℕ} (K : ℝ) (i j : Fin (m + 1)) :
    colexDistance K i j = colexDistance K j i := by
  by_cases hij : i.val < j.val
  · simp [colexDistance, hij, Nat.not_lt.mpr hij.le]
  · by_cases hji : j.val < i.val
    · simp [colexDistance, hji, Nat.not_lt.mpr hji.le]
    · have h : i = j := Fin.ext (Nat.le_antisymm (Nat.not_lt.mp hji) (Nat.not_lt.mp hij))
      subst j
      simp

/-- Squared pure-colex distance data are Hermitian. -/
theorem colexSqData_isHermitian {m : ℕ} (K : ℝ) :
    (colexSqData (m := m) K).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [colexSqData, star_trivial]
  rw [colexDistance_symm]

/-- Squared pure-colex distance data have zero diagonal. -/
@[simp] theorem colexSqData_diag {m : ℕ} (K : ℝ) (i : Fin (m + 1)) :
    colexSqData K i i = 0 := by
  simp [colexSqData]

/-- The adjacent prescribed distance attached to increment `i`. -/
def colexA {m : ℕ} (K : ℝ) (i : Fin m) : ℝ :=
  K + Nat.choose (i.val + 2) 2

/-- One-based adjacent distance, convenient for path-energy formulas. -/
def colexANat (K : ℝ) (j : ℕ) : ℝ :=
  K + Nat.choose (j + 1) 2

/-- Coefficient of the path square between one-based coordinates `j` and
`j+1`; at the final coordinate it is the endpoint correction. -/
noncomputable def colexPathCoeff (K : ℝ) (j : ℕ) : ℝ :=
  colexANat K j ^ 2 / 2 + colexANat K (j + 1) - 1 / 2

/-- One-based diagonal potential in the exact colex path decomposition. -/
noncomputable def colexPotential (K : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then K ^ 2 / 2 - 2
  else if j = 2 then -4
  else (j - 2 : ℕ) * K + (j : ℝ) ^ 3 / 2 - (j : ℝ) ^ 2 - 2 * j

/-- The `Fin`-indexed adjacent distance agrees with its one-based form. -/
@[simp] theorem colexA_eq_colexANat {m : ℕ} (K : ℝ) (i : Fin m) :
    colexA K i = colexANat K (i.val + 1) := by
  rfl

/-- Path coefficients are nonnegative in the coarse colex range. -/
theorem colexPathCoeff_nonneg {K : ℝ} (hK : 10 ≤ K) {j : ℕ} (_hj : 1 ≤ j) :
    0 ≤ colexPathCoeff K j := by
  have hc : (0 : ℝ) ≤ Nat.choose (j + 1 + 1) 2 := by positivity
  have hA : 1 ≤ colexANat K (j + 1) := by
    unfold colexANat
    linarith
  unfold colexPathCoeff
  nlinarith [sq_nonneg (colexANat K j)]

/-- The first path coefficient dominates the quarter-square used by the
two-coordinate coercivity lemma. -/
theorem colexPathCoeff_one_ge {K : ℝ} (hK : 10 ≤ K) :
    K ^ 2 / 4 ≤ colexPathCoeff K 1 := by
  norm_num [colexPathCoeff, colexANat, Nat.choose]
  nlinarith [sq_nonneg (K + 1)]

/-- The first potential has the same quarter-square lower bound. -/
theorem colexPotential_one_ge {K : ℝ} (hK : 10 ≤ K) :
    K ^ 2 / 4 ≤ colexPotential K 1 := by
  simp [colexPotential]
  nlinarith [sq_nonneg (K - 10)]

/-- Exact first-coordinate coefficient identity in the colex path decomposition. -/
theorem colexANat_sq_eq_pathCoeff_add_potential_one (K : ℝ) :
    colexANat K 1 ^ 2 = colexPathCoeff K 1 + colexPotential K 1 := by
  norm_num [colexANat, colexPathCoeff, colexPotential, Nat.choose]
  ring

/-- Exact internal-coordinate coefficient identity in the colex path decomposition. -/
theorem colexANat_sq_eq_pathCoeff_add_potential_add_pathCoeff
    {K : ℝ} {j : ℕ} (hj : 2 ≤ j) :
    colexANat K j ^ 2 =
      colexPathCoeff K (j - 1) + colexPotential K j + colexPathCoeff K j := by
  rcases eq_or_lt_of_le hj with rfl | hj3
  · norm_num [colexANat, colexPathCoeff, colexPotential, Nat.choose]
    ring
  · have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    simp [colexANat, colexPathCoeff, colexPotential, hj1, hj2]
    push_cast [Nat.cast_choose_two]
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_sub (by omega : 2 ≤ j)]
    field_simp
    ring

/-- One adjacent path edge as a sparse symmetric matrix. -/
noncomputable def colexPathEdgeMatrix {m : ℕ} (K : ℝ) (i : Fin (m - 1)) :
    Matrix (Fin m) (Fin m) ℝ :=
  let a : Fin m := ⟨i.val, by omega⟩
  let b : Fin m := ⟨i.val + 1, by omega⟩
  let c := colexPathCoeff K (i.val + 1)
  Matrix.single a a c + Matrix.single b b c -
    Matrix.single a b c - Matrix.single b a c

/-- Sum of all adjacent path-edge matrices. -/
noncomputable def colexPathEnergyMatrix {m : ℕ} (K : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ i : Fin (m - 1), colexPathEdgeMatrix K i

/-- Diagonal matrix of colex potentials. -/
noncomputable def colexPotentialMatrix {m : ℕ} (K : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ i : Fin m, Matrix.single i i (colexPotential K (i.val + 1))

/-- Sparse endpoint correction at the last coordinate. -/
noncomputable def colexEndpointMatrix {m : ℕ} (hm : 0 < m) (K : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.single ⟨m - 1, Nat.sub_lt hm (by norm_num)⟩
    ⟨m - 1, Nat.sub_lt hm (by norm_num)⟩ (colexPathCoeff K m)

/-- Quadratic form of a sparse single-entry matrix. -/
theorem dotProduct_single_mulVec {m : ℕ} (x : Fin m → ℝ) (i j : Fin m) (c : ℝ) :
    star x ⬝ᵥ (Matrix.single i j c *ᵥ x) = x i * c * x j := by
  rw [Matrix.single_mulVec]
  simp only [dotProduct, star_trivial]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro b hb hbi
    simp [hbi]
  · simp

/-- Each sparse adjacent-edge matrix contributes its weighted path square. -/
theorem colexPathEdgeMatrix_quadratic {m : ℕ} (K : ℝ) (x : Fin m → ℝ)
    (i : Fin (m - 1)) :
    star x ⬝ᵥ (colexPathEdgeMatrix K i *ᵥ x) =
      colexPathCoeff K (i.val + 1) *
        (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) ^ 2 := by
  simp only [colexPathEdgeMatrix, Matrix.add_mulVec, Matrix.sub_mulVec,
    dotProduct_add, dotProduct_sub]
  rw [dotProduct_single_mulVec, dotProduct_single_mulVec,
    dotProduct_single_mulVec, dotProduct_single_mulVec]
  ring

/-- Quadratic form of the entire sparse path-energy matrix. -/
theorem colexPathEnergyMatrix_quadratic {m : ℕ} (K : ℝ) (x : Fin m → ℝ) :
    star x ⬝ᵥ (colexPathEnergyMatrix K *ᵥ x) =
      ∑ i : Fin (m - 1), colexPathCoeff K (i.val + 1) *
        (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) ^ 2 := by
  simp only [colexPathEnergyMatrix, Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact colexPathEdgeMatrix_quadratic K x i

/-- Quadratic form of the diagonal potential matrix. -/
theorem colexPotentialMatrix_quadratic {m : ℕ} (K : ℝ) (x : Fin m → ℝ) :
    star x ⬝ᵥ (colexPotentialMatrix K *ᵥ x) =
      ∑ i : Fin m, colexPotential K (i.val + 1) * x i ^ 2 := by
  simp only [colexPotentialMatrix, Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dotProduct_single_mulVec]
  ring

/-- Quadratic form of the endpoint correction. -/
theorem colexEndpointMatrix_quadratic {m : ℕ} (hm : 0 < m) (K : ℝ)
    (x : Fin m → ℝ) :
    star x ⬝ᵥ (colexEndpointMatrix hm K *ᵥ x) =
      colexPathCoeff K m * x ⟨m - 1, Nat.sub_lt hm (by norm_num)⟩ ^ 2 := by
  unfold colexEndpointMatrix
  rw [dotProduct_single_mulVec]
  ring

/-- Upper adjacent entry of the sparse path-energy matrix. -/
theorem colexPathEnergyMatrix_adjacent {m : ℕ} (K : ℝ) (a b : Fin m)
    (hab : a.val + 1 = b.val) :
    colexPathEnergyMatrix K a b = -colexPathCoeff K (a.val + 1) := by
  have ha : a.val < m - 1 := by omega
  let i : Fin (m - 1) := ⟨a.val, ha⟩
  unfold colexPathEnergyMatrix
  rw [Matrix.sum_apply, Finset.sum_eq_single i]
  · have hne : a ≠ b := by intro h; subst b; simp at hab
    simp [colexPathEdgeMatrix, i, Matrix.single_apply, hab, hne, Ne.symm hne]
  · intro k hk hki
    have hv : k.val ≠ a.val := by
      intro h
      apply hki
      exact Fin.ext h
    have hkA : (⟨k.val, by omega⟩ : Fin m) ≠ a := by
      intro h
      exact hv (Fin.ext_iff.mp h)
    have hkB : (⟨k.val + 1, by omega⟩ : Fin m) ≠ b := by
      intro h
      have hval := Fin.ext_iff.mp h
      change k.val + 1 = b.val at hval
      apply hv
      omega
    have hne : a ≠ b := by intro h; subst b; simp at hab
    have hrev : ¬((⟨k.val + 1, by omega⟩ : Fin m) = a ∧
        (⟨k.val, by omega⟩ : Fin m) = b) := by
      rintro ⟨h1, h2⟩
      have hv1 := Fin.ext_iff.mp h1
      have hv2 := Fin.ext_iff.mp h2
      change k.val + 1 = a.val at hv1
      change k.val = b.val at hv2
      omega
    simp [colexPathEdgeMatrix, Matrix.single_apply, hkA, hkB, hne, Ne.symm hne, hrev]
  · simp

/-- The sparse path-energy matrix is symmetric. -/
theorem colexPathEnergyMatrix_isHermitian {m : ℕ} (K : ℝ) :
    (colexPathEnergyMatrix (m := m) K).IsHermitian := by
  unfold colexPathEnergyMatrix
  rw [Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [colexPathEdgeMatrix, Matrix.conjTranspose_single]
  abel

/-- Lower adjacent entry of the sparse path-energy matrix. -/
theorem colexPathEnergyMatrix_adjacent_rev {m : ℕ} (K : ℝ) (a b : Fin m)
    (hba : b.val + 1 = a.val) :
    colexPathEnergyMatrix K a b = -colexPathCoeff K (b.val + 1) := by
  have hsym := (colexPathEnergyMatrix_isHermitian (m := m) K).apply a b
  simp only [star_trivial] at hsym
  rw [← hsym, colexPathEnergyMatrix_adjacent K b a hba]

/-- Distant entries of the sparse path-energy matrix vanish. -/
theorem colexPathEnergyMatrix_distant_zero {m : ℕ} (K : ℝ) (a b : Fin m)
    (hneq : a ≠ b)
    (hadj : ¬(a.val + 1 = b.val ∨ b.val + 1 = a.val)) :
    colexPathEnergyMatrix K a b = 0 := by
  unfold colexPathEnergyMatrix
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have ha0 : (⟨i.val, by omega⟩ : Fin m) ≠ a ∨
      (⟨i.val, by omega⟩ : Fin m) ≠ b := by
    by_contra h
    push_neg at h
    exact hneq (h.1.symm.trans h.2)
  have hb0 : (⟨i.val + 1, by omega⟩ : Fin m) ≠ a ∨
      (⟨i.val + 1, by omega⟩ : Fin m) ≠ b := by
    by_contra h
    push_neg at h
    exact hneq (h.1.symm.trans h.2)
  have hab0 : ¬((⟨i.val, by omega⟩ : Fin m) = a ∧
      (⟨i.val + 1, by omega⟩ : Fin m) = b) := by
    rintro ⟨h1, h2⟩
    apply hadj
    left
    have hv1 := Fin.ext_iff.mp h1
    have hv2 := Fin.ext_iff.mp h2
    change i.val = a.val at hv1
    change i.val + 1 = b.val at hv2
    omega
  have hba0 : ¬((⟨i.val + 1, by omega⟩ : Fin m) = a ∧
      (⟨i.val, by omega⟩ : Fin m) = b) := by
    rintro ⟨h1, h2⟩
    apply hadj
    right
    have hv1 := Fin.ext_iff.mp h1
    have hv2 := Fin.ext_iff.mp h2
    change i.val + 1 = a.val at hv1
    change i.val = b.val at hv2
    omega
  have ha0' : ¬((⟨i.val, by omega⟩ : Fin m) = a ∧
      (⟨i.val, by omega⟩ : Fin m) = b) := by tauto
  have hb0' : ¬((⟨i.val + 1, by omega⟩ : Fin m) = a ∧
      (⟨i.val + 1, by omega⟩ : Fin m) = b) := by tauto
  simp [colexPathEdgeMatrix, Matrix.single_apply, ha0', hb0', hab0, hba0]

/-- Diagonal entry contributed by one path edge. -/
theorem colexPathEdgeMatrix_diag {m : ℕ} (K : ℝ) (i : Fin (m - 1)) (a : Fin m) :
    colexPathEdgeMatrix K i a a =
      if a.val = i.val ∨ a.val = i.val + 1 then colexPathCoeff K (i.val + 1) else 0 := by
  let u : Fin m := ⟨i.val, by omega⟩
  let v : Fin m := ⟨i.val + 1, by omega⟩
  have huv : u ≠ v := by intro h; have := Fin.ext_iff.mp h; simp [u, v] at this
  have hu : u = a ↔ i.val = a.val := by simp [u, Fin.ext_iff]
  have hv : v = a ↔ i.val + 1 = a.val := by simp [v, Fin.ext_iff]
  have huvA : ¬(u = a ∧ v = a) := by
    rintro ⟨h1, h2⟩
    exact huv (h1.trans h2.symm)
  change (Matrix.single u u (colexPathCoeff K (i.val + 1)) +
      Matrix.single v v (colexPathCoeff K (i.val + 1)) -
      Matrix.single u v (colexPathCoeff K (i.val + 1)) -
      Matrix.single v u (colexPathCoeff K (i.val + 1))) a a = _
  simp [Matrix.single_apply, huvA, hu, hv]
  aesop

/-- First diagonal entry of the path-energy matrix. -/
theorem colexPathEnergyMatrix_diag_zero {m : ℕ} (hm : 2 ≤ m) (K : ℝ) :
    colexPathEnergyMatrix K (⟨0, by omega⟩ : Fin m) ⟨0, by omega⟩ =
      colexPathCoeff K 1 := by
  unfold colexPathEnergyMatrix
  rw [Matrix.sum_apply]
  let i : Fin (m - 1) := ⟨0, by omega⟩
  rw [Finset.sum_eq_single i]
  · rw [colexPathEdgeMatrix_diag]
    simp [i]
  · intro k hk hki
    rw [colexPathEdgeMatrix_diag]
    have hkpos : 0 < k.val := by
      by_contra h
      apply hki
      apply Fin.ext
      simp [i]
      omega
    have hkne : 0 ≠ k.val := Ne.symm (Nat.ne_of_gt hkpos)
    simp [hkne]
  · simp

/-- Internal diagonal entry of the path-energy matrix. -/
theorem colexPathEnergyMatrix_diag_internal {m : ℕ} (K : ℝ) (a : Fin m)
    (ha0 : 0 < a.val) (halast : a.val + 1 < m) :
    colexPathEnergyMatrix K a a =
      colexPathCoeff K a.val + colexPathCoeff K (a.val + 1) := by
  unfold colexPathEnergyMatrix
  rw [Matrix.sum_apply]
  let il : Fin (m - 1) := ⟨a.val - 1, by omega⟩
  let ir : Fin (m - 1) := ⟨a.val, by omega⟩
  have hsub : a.val - 1 + 1 = a.val := Nat.sub_add_cancel (by omega)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ il)]
  rw [Finset.sum_eq_single ir]
  · rw [colexPathEdgeMatrix_diag, colexPathEdgeMatrix_diag]
    simp [il, ir, hsub]
    ring
  · intro k hk hkir
    have hkil : k ≠ il := by simpa using hk
    rw [colexPathEdgeMatrix_diag]
    split_ifs with h
    · exfalso
      rcases h with h | h
      · apply hkir; apply Fin.ext; simpa [ir] using h.symm
      · apply hkil; apply Fin.ext; simp [il]; omega
    · rfl
  · intro hnot
    exfalso
    apply hnot
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hir
    have hv := Fin.ext_iff.mp hir
    simp [ir, il] at hv
    omega

/-- Final diagonal entry of the path-energy matrix. -/
theorem colexPathEnergyMatrix_diag_last {m : ℕ} (hm : 2 ≤ m) (K : ℝ) :
    colexPathEnergyMatrix K
      ⟨m - 1, Nat.sub_lt (by omega) (by norm_num)⟩
      ⟨m - 1, Nat.sub_lt (by omega) (by norm_num)⟩ =
      colexPathCoeff K (m - 1) := by
  unfold colexPathEnergyMatrix
  rw [Matrix.sum_apply]
  have hi : m - 2 < m - 1 := by omega
  have hsub : m - 2 + 1 = m - 1 := by omega
  let i : Fin (m - 1) := ⟨m - 2, hi⟩
  rw [Finset.sum_eq_single i]
  · rw [colexPathEdgeMatrix_diag]
    simp [i, hsub]
  · intro k hk hki
    rw [colexPathEdgeMatrix_diag]
    split_ifs with h
    · exfalso
      apply hki
      apply Fin.ext
      rcases h with h | h <;> simp at h <;> simp [i] <;> omega
    · rfl
  · simp

/-- Entries of the diagonal potential matrix. -/
theorem colexPotentialMatrix_apply {m : ℕ} (K : ℝ) (a b : Fin m) :
    colexPotentialMatrix K a b =
      if a = b then colexPotential K (a.val + 1) else 0 := by
  unfold colexPotentialMatrix
  rw [Matrix.sum_apply]
  by_cases hab : a = b
  · subst b
    rw [Finset.sum_eq_single a]
    · simp
    · intro k hk hka
      simp [Matrix.single_apply, hka]
    · simp
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Matrix.single_apply]
    split_ifs with h
    · exact False.elim (hab (h.1.symm.trans h.2))
    · rfl

/-- In increasing order, the prescribed distance is offset plus its colex label. -/
theorem colexDistance_of_lt {m : ℕ} {K : ℝ} {i j : Fin (m + 1)} (h : i.val < j.val) :
    colexDistance K i j = K + colexLabel i.val j.val := by
  simp [colexDistance, h]

/-- The distance across one increment is `colexA`. -/
theorem colexDistance_increment {m : ℕ} (K : ℝ) (i : Fin m) :
    colexDistance K i.castSucc i.succ = colexA K i := by
  have hlt : i.castSucc.val < i.succ.val := by simp
  rw [colexDistance_of_lt hlt]
  have hlabel : colexLabel i.castSucc.val i.succ.val = Nat.choose (i.val + 2) 2 := by
    simpa using colexLabel_last (i.val + 1) (by omega)
  rw [hlabel]
  rfl

/-- The diagonal increment-Gram entry is the square of the adjacent distance. -/
theorem colexIncrementGram_diag {m : ℕ} (K : ℝ) (i : Fin m) :
    incrementGram (colexSqData (m := m) K) i i = colexA K i ^ 2 := by
  have hlt : i.castSucc.val < i.succ.val := by simp
  have hd := colexDistance_increment K i
  have hdr : colexDistance K i.succ i.castSucc = colexA K i := by
    rw [colexDistance_symm, hd]
  simp only [incrementGram, colexSqData, colexDistance_self, hd, hdr, colexA]
  ring

/-- The upper adjacent increment-Gram entry has the exact path coefficient. -/
theorem colexIncrementGram_adjacent {m : ℕ} (K : ℝ) (i j : Fin m)
    (hij : i.val + 1 = j.val) :
    incrementGram (colexSqData (m := m) K) i j =
      -(colexA K i) ^ 2 / 2 - colexA K j + 1 / 2 := by
  have hsame : i.succ = j.castSucc := Fin.ext hij
  have hd11 : colexDistance K i.succ j.succ = colexA K j := by
    rw [hsame]
    exact colexDistance_increment K j
  have hd00 : colexDistance K i.castSucc j.castSucc = colexA K i := by
    rw [← hsame]
    exact colexDistance_increment K i
  have hlt02 : i.castSucc.val < j.succ.val := by simp only [Fin.val_castSucc, Fin.val_succ]; omega
  have hchoose : Nat.choose (j.val + 2) 2 = Nat.choose (j.val + 1) 2 + (j.val + 1) := by
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
    norm_num
    omega
  have hlabel02 :
      colexLabel i.castSucc.val j.succ.val + 1 = Nat.choose (j.val + 2) 2 := by
    simp only [colexLabel, Fin.val_castSucc, Fin.val_succ]
    rw [hchoose]
    omega
  have hd01 : colexDistance K i.castSucc j.succ = colexA K j - 1 := by
    rw [colexDistance_of_lt hlt02]
    simp only [colexA]
    have hlabel02R :
        (colexLabel i.castSucc.val j.succ.val : ℝ) + 1 =
          (Nat.choose (j.val + 2) 2 : ℝ) := by exact_mod_cast hlabel02
    norm_num [Nat.add_comm] at hlabel02R ⊢
    linarith
  have hdj := colexDistance_increment K j
  simp only [incrementGram, colexSqData, hd00, hd01, hsame, hdj,
    colexDistance_self]
  ring

/-- A distant upper-triangular increment-Gram entry is minus the zero-based larger index. -/
theorem colexIncrementGram_distant {m : ℕ} (K : ℝ) (i j : Fin m)
    (hij : i.val + 1 < j.val) :
    incrementGram (colexSqData (m := m) K) i j = -(j.val : ℝ) := by
  have h11 : i.succ.val < j.succ.val := by simp only [Fin.val_succ]; omega
  have h10 : i.succ.val < j.castSucc.val := by
    simp only [Fin.val_succ, Fin.val_castSucc]
    exact hij
  have h01 : i.castSucc.val < j.succ.val := by simp only [Fin.val_castSucc, Fin.val_succ]; omega
  have h00 : i.castSucc.val < j.castSucc.val := by
    simp only [Fin.val_castSucc]
    omega
  have hchoose : Nat.choose (j.val + 1) 2 = Nat.choose j.val 2 + j.val := by
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
    norm_num
    omega
  simp only [incrementGram, colexSqData]
  rw [colexDistance_of_lt h11, colexDistance_of_lt h10,
    colexDistance_of_lt h01, colexDistance_of_lt h00]
  simp only [colexLabel, Fin.val_succ, Fin.val_castSucc]
  rw [hchoose]
  push_cast
  ring

/-- The distant lower-triangular formula follows by symmetry. -/
theorem colexIncrementGram_distant_rev {m : ℕ} (K : ℝ) (i j : Fin m)
    (hji : j.val + 1 < i.val) :
    incrementGram (colexSqData (m := m) K) i j = -(i.val : ℝ) := by
  have hherm := incrementGram_isHermitian (colexSqData (m := m) K)
    (colexSqData_isHermitian K)
  have h := hherm.apply i j
  simp only [star_trivial] at h
  rw [← h, colexIncrementGram_distant K j i hji]

/-- The diagonal and first off-diagonals of the colex increment Gram matrix. -/
noncomputable def colexTridiagonal {m : ℕ} (K : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if i = j then incrementGram (colexSqData K) i j
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
      incrementGram (colexSqData K) i j
    else 0

/-- The positive-sign dense remainder, so that `B = T - R`. -/
noncomputable def colexRemainder {m : ℕ} (K : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  colexTridiagonal K - incrementGram (colexSqData K)

/-- The tridiagonal truncation remains Hermitian. -/
theorem colexTridiagonal_isHermitian {m : ℕ} (K : ℝ) :
    (colexTridiagonal (m := m) K).IsHermitian := by
  have hB := incrementGram_isHermitian (colexSqData (m := m) K)
    (colexSqData_isHermitian K)
  apply Matrix.IsHermitian.ext
  intro i j
  have hij := hB.apply i j
  simp only [star_trivial] at hij ⊢
  by_cases hEq : i = j
  · subst j
    simp [colexTridiagonal]
  · have hEq' : j ≠ i := Ne.symm hEq
    by_cases hAdj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have hAdj' : j.val + 1 = i.val ∨ i.val + 1 = j.val := hAdj.symm
      simp [colexTridiagonal, hEq, hEq', hAdj, hAdj', hij]
    · have hAdj' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := by tauto
      simp [colexTridiagonal, hEq, hEq', hAdj, hAdj']

/-- The dense remainder is Hermitian. -/
theorem colexRemainder_isHermitian {m : ℕ} (K : ℝ) :
    (colexRemainder (m := m) K).IsHermitian := by
  exact (colexTridiagonal_isHermitian K).sub
    (incrementGram_isHermitian (colexSqData K) (colexSqData_isHermitian K))

/-- The increment Gram matrix is tridiagonal part minus dense remainder. -/
theorem colex_incrementGram_eq_tridiagonal_sub_remainder {m : ℕ} (K : ℝ) :
    incrementGram (colexSqData (m := m) K) =
      colexTridiagonal K - colexRemainder K := by
  ext i j
  simp [colexRemainder]

/-- The remainder vanishes on its diagonal. -/
@[simp] theorem colexRemainder_diag {m : ℕ} (K : ℝ) (i : Fin m) :
    colexRemainder K i i = 0 := by
  simp [colexRemainder, colexTridiagonal]

/-- The remainder vanishes on the upper adjacent diagonal. -/
theorem colexRemainder_adjacent {m : ℕ} (K : ℝ) (i j : Fin m)
    (hij : i.val + 1 = j.val) : colexRemainder K i j = 0 := by
  have hne : i ≠ j := by intro h; subst j; simp at hij
  simp [colexRemainder, colexTridiagonal, hne, hij]

/-- A distant upper-triangular remainder entry is the zero-based larger index. -/
theorem colexRemainder_distant {m : ℕ} (K : ℝ) (i j : Fin m)
    (hij : i.val + 1 < j.val) : colexRemainder K i j = (j.val : ℝ) := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hadj : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
  simp [colexRemainder, colexTridiagonal, hne, hadj,
    colexIncrementGram_distant K i j hij]

/-- A distant lower-triangular remainder entry is the zero-based larger index. -/
theorem colexRemainder_distant_rev {m : ℕ} (K : ℝ) (i j : Fin m)
    (hji : j.val + 1 < i.val) : colexRemainder K i j = (i.val : ℝ) := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hadj : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
  simp [colexRemainder, colexTridiagonal, hne, hadj,
    colexIncrementGram_distant_rev K i j hji]

/-- The tridiagonal matrix is exactly path energy plus potentials and the endpoint correction. -/
theorem colexTridiagonal_eq_path_potential_endpoint {m : ℕ} (hm : 2 ≤ m) (K : ℝ) :
    colexTridiagonal K = colexPathEnergyMatrix K + colexPotentialMatrix K +
      colexEndpointMatrix (lt_of_lt_of_le Nat.zero_lt_two hm) K := by
  ext a b
  by_cases hab : a = b
  · subst b
    have hT : colexTridiagonal K a a = colexANat K (a.val + 1) ^ 2 := by
      simp [colexTridiagonal, colexIncrementGram_diag, colexA_eq_colexANat]
    rw [hT, Matrix.add_apply, Matrix.add_apply, colexPotentialMatrix_apply]
    simp only [if_pos]
    by_cases ha0 : a.val = 0
    · have ha : a = ⟨0, by omega⟩ := Fin.ext ha0
      rw [ha]
      rw [colexPathEnergyMatrix_diag_zero hm]
      have hm1 : m - 1 ≠ 0 := by omega
      simp [colexEndpointMatrix, Matrix.single_apply, hm1]
      rw [colexANat_sq_eq_pathCoeff_add_potential_one]
    · by_cases halast : a.val = m - 1
      · have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_two hm
        have ha : a = ⟨m - 1, Nat.sub_lt hmpos (by norm_num)⟩ := Fin.ext halast
        rw [ha]
        rw [colexPathEnergyMatrix_diag_last hm]
        simp [colexEndpointMatrix, Matrix.single_apply]
        have hcoeff := colexANat_sq_eq_pathCoeff_add_potential_add_pathCoeff
          (K := K) (j := m) hm
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hcoeff
      · have ha0' : 0 < a.val := Nat.pos_of_ne_zero ha0
        have halast' : a.val + 1 < m := by omega
        rw [colexPathEnergyMatrix_diag_internal K a ha0' halast']
        have hlastFin : (⟨m - 1, Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_two hm)
            (by norm_num)⟩ : Fin m) ≠ a := by
          intro h
          apply halast
          exact (Fin.ext_iff.mp h).symm
        simp [colexEndpointMatrix, Matrix.single_apply, hlastFin]
        have hcoeff := colexANat_sq_eq_pathCoeff_add_potential_add_pathCoeff
          (K := K) (j := a.val + 1) (by omega)
        simpa [Nat.add_sub_cancel, add_assoc, add_left_comm, add_comm] using hcoeff
  · have hpot : colexPotentialMatrix K a b = 0 := by
      rw [colexPotentialMatrix_apply]
      simp [hab]
    have hend : colexEndpointMatrix (lt_of_lt_of_le Nat.zero_lt_two hm) K a b = 0 := by
      unfold colexEndpointMatrix
      rw [Matrix.single_apply]
      split_ifs with h
      · exact False.elim (hab (h.1.symm.trans h.2))
      · rfl
    rw [Matrix.add_apply, Matrix.add_apply, hpot, hend, add_zero]
    by_cases hadj : a.val + 1 = b.val
    · rw [colexPathEnergyMatrix_adjacent K a b hadj]
      have hT : colexTridiagonal K a b =
          -(colexPathCoeff K (a.val + 1)) := by
        simp [colexTridiagonal, hab, hadj, colexIncrementGram_adjacent,
          colexPathCoeff, colexA_eq_colexANat]
        ring
      simpa using hT
    · by_cases hrev : b.val + 1 = a.val
      · rw [colexPathEnergyMatrix_adjacent_rev K a b hrev]
        have hsym := (colexTridiagonal_isHermitian K).apply a b
        simp only [star_trivial] at hsym
        rw [← hsym]
        simp [colexTridiagonal, Ne.symm hab, hrev, colexIncrementGram_adjacent,
          colexPathCoeff, colexA_eq_colexANat]
        ring
      · rw [colexPathEnergyMatrix_distant_zero K a b hab (by tauto)]
        simp [colexTridiagonal, hab, hadj, hrev]

/-- Exact finite path-energy identity for the colex tridiagonal quadratic form. -/
theorem colex_tridiagonal_quadratic_eq {m : ℕ} (hm : 2 ≤ m) (K : ℝ)
    (x : Fin m → ℝ) :
    star x ⬝ᵥ (colexTridiagonal K *ᵥ x) =
      (∑ i : Fin (m - 1), colexPathCoeff K (i.val + 1) *
        (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) ^ 2) +
      (∑ i : Fin m, colexPotential K (i.val + 1) * x i ^ 2) +
      colexPathCoeff K m *
        x ⟨m - 1, Nat.sub_lt (by omega) (by norm_num)⟩ ^ 2 := by
  rw [colexTridiagonal_eq_path_potential_endpoint hm]
  simp only [Matrix.add_mulVec, dotProduct_add]
  rw [colexPathEnergyMatrix_quadratic, colexPotentialMatrix_quadratic,
    colexEndpointMatrix_quadratic]

/-- The one-based coercive weight for the pure-colex quadratic form. -/
noncomputable def colexWeight (K : ℝ) (j : ℕ) : ℝ :=
  if j ≤ 2 then K ^ 2 / 24 else (K * j + j ^ 3) / 24

/-- The diagonal comparison form used in pure-colex coercivity. -/
noncomputable def colexQ {m : ℕ} (K : ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ i, colexWeight K (i.val + 1) * x i ^ 2

/-- Every pure-colex comparison weight is positive once `K ≥ 10`. -/
theorem colexWeight_pos {K : ℝ} (hK : 10 ≤ K) (j : ℕ) (hj : 1 ≤ j) :
    0 < colexWeight K j := by
  unfold colexWeight
  split_ifs with h
  · have hKpos : 0 < K := by linarith
    positivity
  · have hjR : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
    have hKpos : 0 < K := by linarith
    positivity

/-- The pure-colex comparison form is nonnegative. -/
theorem colexQ_nonneg {m : ℕ} {K : ℝ} (hK : 10 ≤ K) (x : Fin m → ℝ) :
    0 ≤ colexQ K x := by
  unfold colexQ
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (colexWeight_pos hK _ (by omega)).le (sq_nonneg _)

/-- The pure-colex comparison form is strictly positive away from zero. -/
theorem colexQ_pos {m : ℕ} {K : ℝ} (hK : 10 ≤ K) {x : Fin m → ℝ}
    (hx : x ≠ 0) : 0 < colexQ K x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  unfold colexQ
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (colexWeight_pos hK _ (by omega)).le (sq_nonneg _)
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    exact mul_pos (colexWeight_pos hK _ (by omega)) (sq_pos_of_ne_zero hi)

/-- Every potential from the third coordinate onward dominates its comparison weight. -/
theorem colexPotential_ge_weight {K : ℝ} (hK : 10 ≤ K) {j : ℕ} (hj : 3 ≤ j) :
    colexWeight K j ≤ colexPotential K j := by
  rcases eq_or_lt_of_le hj with rfl | hj4
  · have h := colex_potential_three (K := K) (by linarith)
    norm_num [colexWeight, colexPotential] at h ⊢
    linarith
  · have h := colex_potential_ge_four (K := K) (i := (j : ℝ)) hK
      (by exact_mod_cast hj4)
    simp [colexWeight, colexPotential, show ¬j ≤ 2 by omega,
      show j ≠ 1 by omega, show j ≠ 2 by omega]
    push_cast
    rw [Nat.cast_sub (by omega : 2 ≤ j)]
    nlinarith

/-- All path edges except the first contribute a nonnegative quadratic form. -/
theorem colexPathEnergy_tail_nonneg {m : ℕ} (hm : 2 ≤ m) {K : ℝ} (hK : 10 ≤ K)
    (x : Fin m → ℝ) :
    0 ≤ ∑ i ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin (m - 1))),
      colexPathCoeff K (i.val + 1) *
        (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) ^ 2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (colexPathCoeff_nonneg hK (by omega)) (sq_nonneg _)

/-- Pure-colex tridiagonal coercivity against the diagonal comparison form. -/
theorem colex_tridiagonal_ge_Q {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K) (x : Fin m → ℝ) :
    colexQ K x ≤ star x ⬝ᵥ (colexTridiagonal K *ᵥ x) := by
  let z0 : Fin m := ⟨0, by omega⟩
  let z1 : Fin m := ⟨1, by omega⟩
  let e0 : Fin (m - 1) := ⟨0, by omega⟩
  have hc1 := colexPathCoeff_one_ge (K := K) hK
  have hv1 := colexPotential_one_ge (K := K) hK
  have hfirst :
      colexPathCoeff K 1 * (x z0 - x z1) ^ 2 +
          colexPotential K 1 * x z0 ^ 2 + colexPotential K 2 * x z1 ^ 2 ≥
        K ^ 2 / 24 * (x z0 ^ 2 + x z1 ^ 2) := by
    have hbase := colex_first_two_coercivity (K := K) (s := x z0) (t := x z1) hK
    have hc : K ^ 2 / 4 * (x z0 - x z1) ^ 2 ≤
        colexPathCoeff K 1 * (x z0 - x z1) ^ 2 :=
      mul_le_mul_of_nonneg_right hc1 (sq_nonneg _)
    have hv : K ^ 2 / 4 * x z0 ^ 2 ≤ colexPotential K 1 * x z0 ^ 2 :=
      mul_le_mul_of_nonneg_right hv1 (sq_nonneg _)
    norm_num [colexPotential] at hbase hv ⊢
    nlinarith
  have htailPath := colexPathEnergy_tail_nonneg hm hK x
  have hend : 0 ≤ colexPathCoeff K m *
      x ⟨m - 1, Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_two hm) (by norm_num)⟩ ^ 2 :=
    mul_nonneg (colexPathCoeff_nonneg hK (by omega)) (sq_nonneg _)
  have hpotTail :
      ∑ i ∈ (Finset.univ.erase z0).erase z1,
          colexWeight K (i.val + 1) * x i ^ 2 ≤
      ∑ i ∈ (Finset.univ.erase z0).erase z1,
          colexPotential K (i.val + 1) * x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi1 := Finset.mem_erase.mp hi
    have hi0 := Finset.mem_erase.mp hi1.2
    have hne1 : i ≠ z1 := hi1.1
    have hne0 : i ≠ z0 := hi0.1
    have hj : 3 ≤ i.val + 1 := by
      simp [z0, z1, Fin.ext_iff] at hne0 hne1
      omega
    exact mul_le_mul_of_nonneg_right (colexPotential_ge_weight hK hj) (sq_nonneg _)
  rw [colex_tridiagonal_quadratic_eq hm]
  unfold colexQ
  have hpathSplit := Finset.sum_erase_add (Finset.univ : Finset (Fin (m - 1)))
    (fun i => colexPathCoeff K (i.val + 1) *
      (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) ^ 2) (Finset.mem_univ e0)
  have hq0 := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
    (fun i => colexWeight K (i.val + 1) * x i ^ 2) (Finset.mem_univ z0)
  have hq1 := Finset.sum_erase_add ((Finset.univ : Finset (Fin m)).erase z0)
    (fun i => colexWeight K (i.val + 1) * x i ^ 2) (a := z1) (by
      apply Finset.mem_erase.mpr
      exact ⟨by simp [z0, z1, Fin.ext_iff], Finset.mem_univ _⟩)
  have hp0 := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
    (fun i => colexPotential K (i.val + 1) * x i ^ 2) (Finset.mem_univ z0)
  have hp1 := Finset.sum_erase_add ((Finset.univ : Finset (Fin m)).erase z0)
    (fun i => colexPotential K (i.val + 1) * x i ^ 2) (a := z1) (by
      apply Finset.mem_erase.mpr
      exact ⟨by simp [z0, z1, Fin.ext_iff], Finset.mem_univ _⟩)
  rw [← hq0, ← hq1, ← hpathSplit, ← hp0, ← hp1]
  have hw1 : colexWeight K 1 = K ^ 2 / 24 := by simp [colexWeight]
  have hw2 : colexWeight K 2 = K ^ 2 / 24 := by simp [colexWeight]
  dsimp [e0, z0, z1] at hfirst htailPath hpotTail hend ⊢
  rw [hw1, hw2]
  nlinarith

/-- Young's inequality with an explicit positive weight. -/
theorem two_mul_le_weighted_sq {A C lambda : ℝ} (hlambda : 0 < lambda) :
    2 * A * C ≤ lambda * A ^ 2 + C ^ 2 / lambda := by
  have hsquare : 0 ≤ (lambda * A - C) ^ 2 := sq_nonneg _
  have hinv : 0 < lambda⁻¹ := inv_pos.mpr hlambda
  have hscaled := mul_nonneg hinv.le hsquare
  field_simp [hlambda.ne'] at hscaled ⊢
  nlinarith

/-- Reciprocal-weight sum controlling the unweighted absolute sum. -/
noncomputable def colexS0 {m : ℕ} (K : ℝ) : ℝ :=
  ∑ i : Fin m, (colexWeight K (i.val + 1))⁻¹

/-- Reciprocal-weight sum controlling the one-based indexed absolute sum. -/
noncomputable def colexS2 {m : ℕ} (K : ℝ) : ℝ :=
  ∑ i : Fin m, ((i.val + 1 : ℝ) ^ 2 / colexWeight K (i.val + 1))

/-- Weighted Cauchy bound for the sum of absolute coordinates. -/
theorem colex_abs_sum_sq_le {m : ℕ} {K : ℝ} (hK : 10 ≤ K) (x : Fin m → ℝ) :
    (∑ i, |x i|) ^ 2 ≤ colexS0 (m := m) K * colexQ K x := by
  unfold colexS0 colexQ
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i hi
    exact inv_nonneg.mpr (colexWeight_pos hK _ (by omega)).le
  · intro i hi
    exact mul_nonneg (colexWeight_pos hK _ (by omega)).le (sq_nonneg _)
  · intro i hi
    have hw := (colexWeight_pos hK (i.val + 1) (by omega)).ne'
    rw [sq_abs]
    field_simp [hw]
    exact le_rfl

/-- Weighted Cauchy bound for the one-based indexed absolute sum. -/
theorem colex_indexed_abs_sum_sq_le {m : ℕ} {K : ℝ} (hK : 10 ≤ K)
    (x : Fin m → ℝ) :
    (∑ i, (i.val + 1 : ℝ) * |x i|) ^ 2 ≤ colexS2 (m := m) K * colexQ K x := by
  unfold colexS2 colexQ
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i hi
    exact div_nonneg (sq_nonneg _) (colexWeight_pos hK _ (by omega)).le
  · intro i hi
    exact mul_nonneg (colexWeight_pos hK _ (by omega)).le (sq_nonneg _)
  · intro i hi
    have hw := (colexWeight_pos hK (i.val + 1) (by omega)).ne'
    rw [mul_pow, sq_abs]
    field_simp [hw]
    exact le_rfl

/-- Every remainder entry is bounded by the sum of its one-based indices. -/
theorem colexRemainder_abs_entry_le {m : ℕ} (K : ℝ) (i j : Fin m) :
    |colexRemainder K i j| ≤ (i.val + 1 : ℝ) + (j.val + 1 : ℝ) := by
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · by_cases hadj : i.val + 1 = j.val
    · rw [colexRemainder_adjacent K i j hadj]
      simp
      positivity
    · have hdist : i.val + 1 < j.val := by omega
      rw [colexRemainder_distant K i j hdist]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := by positivity
      linarith
  · have heq : i = j := Fin.ext hij
    subst j
    simp
    positivity
  · by_cases hadj : j.val + 1 = i.val
    · have hzero : colexRemainder K j i = 0 := colexRemainder_adjacent K j i hadj
      have hsym := (colexRemainder_isHermitian K).apply i j
      simp only [star_trivial] at hsym
      rw [← hsym, hzero]
      simp
      positivity
    · have hdist : j.val + 1 < i.val := by omega
      rw [colexRemainder_distant_rev K i j hdist]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have hj0 : (0 : ℝ) ≤ (j.val : ℝ) := by positivity
      linarith

/-- The dense colex remainder is controlled by the product of the plain and
one-based weighted `ℓ¹` norms. -/
theorem colex_remainder_quadratic_abs_le_product {m : ℕ} (K : ℝ)
    (x : Fin m → ℝ) :
    |star x ⬝ᵥ (colexRemainder K *ᵥ x)| ≤
      2 * (∑ i, |x i|) * (∑ i, (i.val + 1 : ℝ) * |x i|) := by
  rw [dotProduct]
  simp only [mulVec, star_trivial]
  calc
    |∑ i, x i * ∑ j, colexRemainder K i j * x j| ≤
        ∑ i, |x i * ∑ j, colexRemainder K i j * x j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ i, |x i| * ∑ j, |colexRemainder K i j * x j| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
            (abs_nonneg _)
    _ ≤ ∑ i, |x i| * ∑ j,
          (((i.val + 1 : ℝ) + (j.val + 1 : ℝ)) * |x j|) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro j hj
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (colexRemainder_abs_entry_le K i j)
              (abs_nonneg _)
          · exact abs_nonneg _
    _ = 2 * (∑ i, |x i|) * (∑ i, (i.val + 1 : ℝ) * |x i|) := by
          let w : Fin m → ℝ := fun i => (i.val + 1 : ℝ)
          change (∑ i, |x i| * ∑ j, (w i + w j) * |x j|) =
            2 * (∑ i, |x i|) * (∑ i, w i * |x i|)
          simp_rw [add_mul, Finset.sum_add_distrib, mul_add]
          have h1 : (∑ i, |x i| * ∑ j, w i * |x j|) =
              (∑ i, w i * |x i|) * (∑ j, |x j|) := by
            calc
              ∑ i, |x i| * ∑ j, w i * |x j| =
                  ∑ i, (w i * |x i|) * ∑ j, |x j| := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [← Finset.mul_sum]
                    ring
              _ = (∑ i, w i * |x i|) * (∑ j, |x j|) := by
                    rw [Finset.sum_mul]
          have h2 : (∑ i, |x i| * ∑ j, w j * |x j|) =
              (∑ i, |x i|) * (∑ j, w j * |x j|) := by
            rw [Finset.sum_mul]
          rw [Finset.sum_add_distrib, h1, h2]
          ring

/-- The real harmonic number is at least one once its index is nonzero. -/
theorem one_le_harmonic_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ (harmonic n : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  have hmem : 1 ∈ Finset.Icc 1 n := by simp [hn]
  have hnonneg : ∀ i ∈ Finset.Icc 1 n, (0 : ℝ) ≤ (i : ℝ)⁻¹ := by
    intro i hi
    positivity
  have h := Finset.single_le_sum hnonneg hmem
  norm_num at h ⊢
  exact h

/-- A uniform reciprocal-weight bound, deliberately coarse at the first two
coordinates so that no finite-sum split is needed. -/
theorem colexWeight_inv_le {K : ℝ} (hK : 10 ≤ K) {j : ℕ} (hj : 1 ≤ j) :
    (colexWeight K j)⁻¹ ≤ 29 / (K * j) := by
  have hKpos : 0 < K := by linarith
  have hjR : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  unfold colexWeight
  split_ifs with hsmall
  · have hj2R : (j : ℝ) ≤ 2 := by exact_mod_cast hsmall
    rw [inv_div]
    apply (le_div_iff₀ (mul_pos hKpos hjR)).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
    nlinarith
  · have hden : 0 < K * (j : ℝ) + (j : ℝ) ^ 3 := by positivity
    rw [inv_div]
    apply (le_div_iff₀ (mul_pos hKpos hjR)).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (j : ℝ)]

/-- A uniform indexed reciprocal-weight bound. -/
theorem colexIndexSq_div_weight_le {K : ℝ} (hK : 10 ≤ K) {j : ℕ}
    (hj : 1 ≤ j) :
    (j : ℝ) ^ 2 / colexWeight K j ≤ 26 / (j : ℝ) := by
  have hKpos : 0 < K := by linarith
  have hjR : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  unfold colexWeight
  split_ifs with hsmall
  · have hj2R : (j : ℝ) ≤ 2 := by exact_mod_cast hsmall
    apply (le_div_iff₀ hjR).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (div_pos (sq_pos_of_pos hKpos) (by norm_num : (0 : ℝ) < 24))).2
    nlinarith [sq_nonneg (j : ℝ), mul_self_nonneg ((j : ℝ) - 1)]
  · have hden : 0 < (K * (j : ℝ) + (j : ℝ) ^ 3) / 24 := by positivity
    apply (le_div_iff₀ hjR).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (j : ℝ)]

/-- The reciprocal one-based indices carried by `Fin m` form an initial
segment of the real harmonic sum through `m+1`. -/
theorem fin_reciprocal_sum_le_harmonic_succ (m : ℕ) :
    (∑ i : Fin m, ((i.val + 1 : ℝ)⁻¹)) ≤ (harmonic (m + 1) : ℝ) := by
  rw [harmonic]
  push_cast
  have heq : (∑ i : Fin m, ((i.val + 1 : ℝ)⁻¹)) =
      ∑ i ∈ Finset.range m, ((i + 1 : ℝ)⁻¹) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ m))
  intro i hi hnot
  positivity

/-- Coarse harmonic control of the reciprocal comparison weights. -/
theorem colex_S0_le {m : ℕ} {K : ℝ} (hK : 10 ≤ K) :
    colexS0 (m := m) K ≤ 29 * (harmonic (m + 1) : ℝ) / K := by
  have hKpos : 0 < K := by linarith
  unfold colexS0
  calc
    ∑ i : Fin m, (colexWeight K (i.val + 1))⁻¹ ≤
        ∑ i : Fin m, 29 / (K * (i.val + 1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          simpa using colexWeight_inv_le hK (j := i.val + 1)
            (Nat.succ_le_succ (Nat.zero_le i.val))
    _ = (29 / K) * ∑ i : Fin m, ((i.val + 1 : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hj : (0 : ℝ) < (i.val + 1 : ℕ) := by positivity
          field_simp [hKpos.ne', hj.ne']
    _ ≤ (29 / K) * (harmonic (m + 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_left (fin_reciprocal_sum_le_harmonic_succ m)
            (div_nonneg (by norm_num) hKpos.le)
    _ = 29 * (harmonic (m + 1) : ℝ) / K := by ring

/-- Coarse harmonic control of the indexed reciprocal comparison weights. -/
theorem colex_S2_le {m : ℕ} {K : ℝ} (hK : 10 ≤ K) :
    colexS2 (m := m) K ≤ 26 * (harmonic (m + 1) : ℝ) := by
  unfold colexS2
  calc
    ∑ i : Fin m, ((i.val + 1 : ℝ) ^ 2 / colexWeight K (i.val + 1)) ≤
        ∑ i : Fin m, 26 / (i.val + 1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          simpa using colexIndexSq_div_weight_le hK (j := i.val + 1)
            (Nat.succ_le_succ (Nat.zero_le i.val))
    _ = 26 * ∑ i : Fin m, ((i.val + 1 : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [div_eq_mul_inv]
    _ ≤ 26 * (harmonic (m + 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_left (fin_reciprocal_sum_le_harmonic_succ m)
            (by norm_num)

/-- The sqrt-free Young closure bounds the entire dense remainder by `55/64`
of the comparison form. -/
theorem colex_remainder_abs_le_fiftyfive_sixtyfour_Q {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 4096 * (harmonic (m + 1) : ℝ) ^ 2 ≤ K) (x : Fin m → ℝ) :
    |star x ⬝ᵥ (colexRemainder K *ᵥ x)| ≤ (55 / 64 : ℝ) * colexQ K x := by
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
  have hcoef0 : 64 * H * colexS0 (m := m) K ≤ (29 / 64 : ℝ) := by
    have hS0K : colexS0 (m := m) K * K ≤ 29 * H := by
      apply (le_div_iff₀ hKpos).mp at hS0
      nlinarith
    have hscale := mul_le_mul_of_nonneg_left hlarge hS0nonneg
    nlinarith
  have hcoef2 : colexS2 (m := m) K / (64 * H) ≤ (26 / 64 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hHpos)).2
    nlinarith
  have hA2 : A ^ 2 ≤ colexS0 (m := m) K * Q := by
    simpa [A, Q] using colex_abs_sum_sq_le hK x
  have hC2 : C ^ 2 ≤ colexS2 (m := m) K * Q := by
    simpa [C, Q] using colex_indexed_abs_sum_sq_le hK x
  have hYoung := two_mul_le_weighted_sq (A := A) (C := C) (lambda := 64 * H)
    (mul_pos (by norm_num) hHpos)
  have hAQ : 64 * H * A ^ 2 ≤ (29 / 64 : ℝ) * Q := by
    calc
      64 * H * A ^ 2 ≤ 64 * H * (colexS0 (m := m) K * Q) := by
        exact mul_le_mul_of_nonneg_left hA2 (mul_nonneg (by norm_num) hHpos.le)
      _ = (64 * H * colexS0 (m := m) K) * Q := by ring
      _ ≤ (29 / 64 : ℝ) * Q := mul_le_mul_of_nonneg_right hcoef0 hQ
  have hCQ : C ^ 2 / (64 * H) ≤ (26 / 64 : ℝ) * Q := by
    calc
      C ^ 2 / (64 * H) ≤ (colexS2 (m := m) K * Q) / (64 * H) := by
        exact div_le_div_of_nonneg_right hC2 (mul_nonneg (by norm_num) hHpos.le)
      _ = (colexS2 (m := m) K / (64 * H)) * Q := by ring
      _ ≤ (26 / 64 : ℝ) * Q := mul_le_mul_of_nonneg_right hcoef2 hQ
  calc
    |star x ⬝ᵥ (colexRemainder K *ᵥ x)| ≤ 2 * A * C := by
      simpa [A, C] using colex_remainder_quadratic_abs_le_product K x
    _ ≤ 64 * H * A ^ 2 + C ^ 2 / (64 * H) := hYoung
    _ ≤ (29 / 64 : ℝ) * Q + (26 / 64 : ℝ) * Q := add_le_add hAQ hCQ
    _ = (55 / 64 : ℝ) * colexQ K x := by simp [Q]; ring

/-- The pure-colex increment Gram quadratic form retains at least `9/64` of
the diagonal comparison form. -/
theorem colex_incrementGram_quadratic_ge_nine_sixtyfour_Q {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 4096 * (harmonic (m + 1) : ℝ) ^ 2 ≤ K) (x : Fin m → ℝ) :
    (9 / 64 : ℝ) * colexQ K x ≤
      star x ⬝ᵥ (incrementGram (colexSqData (m := m) K) *ᵥ x) := by
  have hT := colex_tridiagonal_ge_Q hm hK x
  have hR := colex_remainder_abs_le_fiftyfive_sixtyfour_Q hm hK hlarge x
  have hRle : star x ⬝ᵥ (colexRemainder K *ᵥ x) ≤
      (55 / 64 : ℝ) * colexQ K x := le_trans (le_abs_self _) hR
  rw [colex_incrementGram_eq_tridiagonal_sub_remainder]
  simp only [Matrix.sub_mulVec, dotProduct_sub]
  linarith

/-- Pure-colex squared-distance data have positive-definite increment Gram
matrix at the explicit coarse harmonic scale. -/
theorem colexIncrementGram_posDef {m : ℕ} (hm : 2 ≤ m)
    {K : ℝ} (hK : 10 ≤ K)
    (hlarge : 4096 * (harmonic (m + 1) : ℝ) ^ 2 ≤ K) :
    (incrementGram (colexSqData (m := m) K)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (incrementGram_isHermitian (colexSqData K) (colexSqData_isHermitian K))
  intro x hx
  have hQ := colexQ_pos hK hx
  have hlower := colex_incrementGram_quadratic_ge_nine_sixtyfour_Q hm hK hlarge x
  nlinarith

/-- Integer offset used by the explicit pure-colex construction. -/
noncomputable def colexOffsetNat (n : ℕ) : ℕ :=
  ⌈4096 * (harmonic n : ℝ) ^ 2⌉₊

/-- The pure-colex offset, viewed as a real number. -/
noncomputable def colexOffset (n : ℕ) : ℝ := colexOffsetNat n

/-- The ceiling offset dominates the harmonic threshold by construction. -/
theorem colexOffset_large (n : ℕ) :
    4096 * (harmonic n : ℝ) ^ 2 ≤ colexOffset n := by
  exact Nat.le_ceil _

/-- In the nontrivial geometric range the explicit offset exceeds ten. -/
theorem colexOffset_ge_ten {n : ℕ} (hn : 1 ≤ n) : 10 ≤ colexOffset n := by
  have hH : (1 : ℝ) ≤ harmonic n := one_le_harmonic_of_one_le hn
  have hlarge := colexOffset_large n
  nlinarith [sq_nonneg ((harmonic n : ℝ) - 1)]

/-- The explicit ceiling offset makes the pure-colex increment Gram matrix
positive definite. -/
theorem colexIncrementGram_posDef_offset {m : ℕ} (hm : 2 ≤ m) :
    (incrementGram (colexSqData (m := m) (colexOffset (m + 1)))).PosDef := by
  exact colexIncrementGram_posDef hm (colexOffset_ge_ten (by omega))
    (colexOffset_large (m + 1))

/-- Prescribed colex distances are nonnegative for every nonnegative offset. -/
theorem colexDistance_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (i j : Fin (m + 1)) : 0 ≤ colexDistance K i j := by
  unfold colexDistance
  split_ifs <;> positivity

/-- Pure-colex data at the explicit integer offset admit an affinely
independent realization with the exact prescribed distances. -/
theorem colex_exact_configuration_exists {m : ℕ} (hm : 2 ≤ m) :
    ∃ p : Fin (m + 1) → EuclideanSpace ℝ (Fin m),
      AffineIndependent ℝ p ∧
      ∀ i j, dist (p i) (p j) = colexDistance (colexOffset (m + 1)) i j := by
  let K := colexOffset (m + 1)
  obtain ⟨p, hpaff, hpdist⟩ :=
    posDef_incrementGram_realizes_in_euclideanSpace
      (colexSqData (m := m) K) (colexSqData_isHermitian K)
      (colexSqData_diag K) (colexIncrementGram_posDef_offset hm)
  refine ⟨p, hpaff, ?_⟩
  intro i j
  have hsquares := hpdist i j
  have hnorm : ‖p i - p j‖ = ‖p j - p i‖ := by
    rw [show p i - p j = -(p j - p i) by abel, norm_neg]
  have hdistSq : dist (p i) (p j) ^ 2 = colexDistance K i j ^ 2 := by
    rw [dist_eq_norm, hnorm]
    exact hsquares
  have hleft : 0 ≤ dist (p i) (p j) := dist_nonneg
  have hright : 0 ≤ colexDistance K i j :=
    colexDistance_nonneg (le_trans (by norm_num) (colexOffset_ge_ten (by omega))) i j
  nlinarith

end Erdos488.Geometry.SeparatedDistances
