module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.Sym.Card

/-!
# Fixed-dimensional separated Euclidean distances

For every natural n at least 68000, there are n distinct points in the single
fixed Euclidean space R^458999. Every nonzero pair distance is at least one;
distances on different unordered non-diagonal edges differ by at least one;
and the diameter is strictly below (37/50)n^2.

This is an existential construction with an explicit sufficient dimension and
threshold. It does not assert the smallest dimension, smallest threshold,
optimal coefficient, or coordinates for each point. This file is the audited
statement surface. Its sole deliberate proof hole identifies the statement
that Comparator must match against a proof in Solution. This Challenge alone
is not a proof.

The definitions and theorem signature below are copied from the MIT-licensed
public release at commit 1e73a12ff1076dd11affadbf619ddbbef587133e.
-/

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

/-- An unordered pair of distinct vertices: an element of Sym2 which is not diagonal. -/
abbrev Edge (ι : Type*) := {e : Sym2 ι // ¬e.IsDiag}

/-- The metric distance between the two endpoints of an unordered pair. -/
noncomputable def edgeDistance {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Sym2 ι → ℝ :=
  Sym2.lift ⟨fun i j => dist (p i) (p j), fun i j => dist_comm _ _⟩

/-- Distances attached to any two different unordered non-diagonal pairs differ by at least one. -/
def SeparatedConfiguration {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Prop :=
  ∀ e f : Edge ι, e ≠ f →
    1 ≤ |edgeDistance p e.1 - edgeDistance p f.1|

end Erdos488.Geometry.SeparatedDistances

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

/-- The full fixed-dimensional construction, including injectivity, minimum
distance, unordered-edge separation, pairwise bound and strict diameter bound. -/
theorem fixed_dimension_erdos_670 (n : ℕ) (hn : 68000 ≤ n) :
    ∃ P : Fin n → EuclideanSpace ℝ (Fin 458999),
      Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
      SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (37 / 50 : ℝ) * (n : ℝ) ^ 2) ∧
      Metric.diam (Set.range P) < (37 / 50 : ℝ) * (n : ℝ) ^ 2 := by
  sorry

end Erdos488.Geometry.SeparatedDistances.FixedDimension
