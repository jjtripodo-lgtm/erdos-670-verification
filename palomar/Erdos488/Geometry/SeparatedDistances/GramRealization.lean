module

public import Erdos488.Geometry.SeparatedDistances.Defs
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators
open Matrix

/-- A two-dimensional finite-difference sum telescopes to its four corners. -/
theorem rectangular_mixed_difference_telescope (F : ℕ → ℕ → ℝ)
    {i j : ℕ} (hij : i ≤ j) :
    (∑ a ∈ Finset.Ico i j, ∑ b ∈ Finset.Ico i j,
      (F (a + 1) (b + 1) - F (a + 1) b - F a (b + 1) + F a b)) =
      F j j - F j i - F i j + F i i := by
  have hinner (a : ℕ) :
      (∑ b ∈ Finset.Ico i j,
        (F (a + 1) (b + 1) - F (a + 1) b - F a (b + 1) + F a b)) =
        (F (a + 1) j - F (a + 1) i) - (F a j - F a i) := by
    have h1 := Finset.sum_Ico_sub (fun b => F (a + 1) b) hij
    have h2 := Finset.sum_Ico_sub (fun b => F a b) hij
    rw [← h1, ← h2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  simp_rw [hinner]
  have hout := Finset.sum_Ico_sub (fun a => F a j - F a i) hij
  rw [hout]
  ring

/-- Symmetric squared-distance data produce a symmetric increment Gram matrix. -/
theorem incrementGram_isHermitian {n : ℕ} (D : SqDistanceData (Fin (n + 1)))
    (hD : D.IsHermitian) : (incrementGram D).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [incrementGram, starRingEnd_apply, star_trivial]
  have h11 := hD.apply i.succ j.succ
  have h10 := hD.apply i.succ j.castSucc
  have h01 := hD.apply i.castSucc j.succ
  have h00 := hD.apply i.castSucc j.castSucc
  simp only [star_trivial] at h11 h10 h01 h00
  rw [← h11, ← h10, ← h01, ← h00]
  ring

/-- For symmetric zero-diagonal data, the block mixed difference is the endpoint value. -/
theorem mixed_difference_block_eq_distance (D : ℕ → ℕ → ℝ)
    (hD : ∀ i j, D i j = D j i) (hdiag : ∀ i, D i i = 0)
    {i j : ℕ} (hij : i ≤ j) :
    (∑ a ∈ Finset.Ico i j, ∑ b ∈ Finset.Ico i j,
      (-(1 / 2 : ℝ) *
        (D (a + 1) (b + 1) - D (a + 1) b - D a (b + 1) + D a b))) =
      D i j := by
  calc
    _ = -(1 / 2 : ℝ) *
        (∑ a ∈ Finset.Ico i j, ∑ b ∈ Finset.Ico i j,
          (D (a + 1) (b + 1) - D (a + 1) b - D a (b + 1) + D a b)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ = -(1 / 2 : ℝ) * (D j j - D j i - D i j + D i i) := by
          rw [rectangular_mixed_difference_telescope D hij]
    _ = D i j := by
      rw [hdiag, hdiag, hD j i]
      ring

/--
Every positive-definite real matrix is the Gram matrix of a linearly
independent family in an `n`-dimensional real inner-product space.  The space
is packaged existentially so later construction lemmas can remain independent
of a particular square-root or Cholesky factorization.
-/
theorem posDef_exists_independent_gram {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E)
      (u : Fin n → E), Matrix.gram ℝ u = B ∧ LinearIndependent ℝ u := by
  letI := B.toNormedAddCommGroup hB
  letI := B.toInnerProductSpace hB.posSemidef
  let u : Fin n → (Fin n → ℝ) := fun i => Pi.single i 1
  have hgram : Matrix.gram ℝ u = B := by
    classical
    ext i j
    change ((B *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1)) = B i j
    rw [Matrix.mulVec_single]
    simp only [MulOpposite.op_one, one_smul, dotProduct, Pi.star_apply,
      star_trivial, Matrix.col_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [hbi]
    · simp
  exact ⟨Fin n → ℝ, inferInstance, inferInstance, u, hgram,
    Pi.linearIndependent_single_one (Fin n) ℝ⟩

/-- A positive-definite Gram realization, with its finite dimension packaged explicitly. -/
theorem posDef_exists_fd_independent_gram {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E)
      (_ : FiniteDimensional ℝ E) (u : Fin n → E),
      Matrix.gram ℝ u = B ∧ LinearIndependent ℝ u ∧ Module.finrank ℝ E = n := by
  letI := B.toNormedAddCommGroup hB
  letI := B.toInnerProductSpace hB.posSemidef
  let u : Fin n → (Fin n → ℝ) := fun i => Pi.single i 1
  have hgram : Matrix.gram ℝ u = B := by
    classical
    ext i j
    change ((B *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1)) = B i j
    rw [Matrix.mulVec_single]
    simp only [MulOpposite.op_one, one_smul, dotProduct, Pi.star_apply,
      star_trivial, Matrix.col_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [hbi]
    · simp
  haveI : FiniteDimensional ℝ (Fin n → ℝ) := inferInstance
  have hfinrank : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  exact ⟨Fin n → ℝ, inferInstance, inferInstance, inferInstance, u, hgram,
    Pi.linearIndependent_single_one (Fin n) ℝ, hfinrank⟩

/-- The squared norm of a finite block sum is the corresponding double Gram sum. -/
theorem norm_sq_block_sum_eq_gram_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : ℕ → E) (i j : ℕ) :
    ‖∑ a ∈ Finset.Ico i j, u a‖ ^ 2 =
      ∑ a ∈ Finset.Ico i j, ∑ b ∈ Finset.Ico i j, Matrix.gram ℝ u a b := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, Matrix.gram_apply]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact real_inner_comm _ _

/-- Successive partial sums differ by precisely the intervening block of increments. -/
theorem partial_sum_sub_partial_sum {E : Type*} [AddCommGroup E]
    (u : ℕ → E) {i j : ℕ} (hij : i ≤ j) :
    (∑ a ∈ Finset.range j, u a) - (∑ a ∈ Finset.range i, u a) =
      ∑ a ∈ Finset.Ico i j, u a := by
  rw [Finset.sum_Ico_eq_sub u hij]

end Erdos488.Geometry.SeparatedDistances
