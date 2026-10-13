module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
Definitions for the unrestricted-dimensional separated Euclidean distance problem.

The development uses an explicit construction surface first.  `Separated` records
unit separation between distances belonging to distinct unordered pairs; the
increment Gram construction is developed in later modules.
-/

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators

/-- The colexicographic edge label, indexed by the smaller and larger endpoints. -/
def colexLabel (i j : ℕ) : ℕ := Nat.choose j 2 + i + 1

/-- The gap-seeded/colex hybrid label used in the square-root-log construction. -/
def hybridLabel (r i j : ℕ) : ℕ :=
  if j < r then
    let δ := j - i
    (δ - 1) * r - δ * (δ - 1) / 2 + i + 1
  else
    colexLabel i j

/-- Squared-distance data on a finite vertex type. -/
abbrev SqDistanceData (ι : Type*) := Matrix ι ι ℝ

/-- Finite-difference increment Gram matrix based at consecutive vertices. -/
noncomputable def incrementGram {n : ℕ} (D : SqDistanceData (Fin (n + 1))) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    -(1 / 2 : ℝ) *
      (D i.succ j.succ - D i.succ j.castSucc - D i.castSucc j.succ + D i.castSucc j.castSucc)

/-- Unit separation of all distances attached to distinct unordered pairs. -/
def PairwiseDistanceSeparated {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Prop :=
  ∀ ⦃i j k l : ι⦄, ({i, j} : Set ι) ≠ {k, l} →
    1 ≤ |dist (p i) (p j) - dist (p k) (p l)|

/-- An unordered pair of distinct vertices. -/
abbrev Edge (ι : Type*) := {e : Sym2 ι // ¬e.IsDiag}

/-- Distance attached to an unordered pair. -/
noncomputable def edgeDistance {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Sym2 ι → ℝ :=
  Sym2.lift ⟨fun i j => dist (p i) (p j), fun i j => dist_comm _ _⟩

/-- Publication-facing unit-separation condition on the unordered edge set. -/
def SeparatedConfiguration {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Prop :=
  ∀ e f : Edge ι, e ≠ f →
    1 ≤ |edgeDistance p e.1 - edgeDistance p f.1|

/-- The finite set of distances belonging to distinct unordered pairs. -/
noncomputable def edgeDistances {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [PseudoMetricSpace E] (p : ι → E) : Finset ℝ :=
  Finset.univ.image (fun e : Edge ι => edgeDistance p e.1)

end Erdos488.Geometry.SeparatedDistances
