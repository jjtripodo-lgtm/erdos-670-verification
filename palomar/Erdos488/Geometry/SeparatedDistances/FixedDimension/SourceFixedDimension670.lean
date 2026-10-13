module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceActualSeparation
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceActualDiameter
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceAllNEmbedding

@[expose] public section

/-! The unconditional fixed-dimensional Euclidean construction for the
written Erdős #670 candidate. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

private theorem finite_range_diam_lt_of_pairwise_lt {ι E : Type*}
    [Fintype ι] [Nonempty ι] [PseudoMetricSpace E]
    (P : ι → E) (C : ℝ) (h : ∀ a b, dist (P a) (P b) < C) :
    Metric.diam (Set.range P) < C := by
  let s : Finset (ι × ι) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  let B := s.sup' hs (fun ab => dist (P ab.1) (P ab.2))
  have hB (a b : ι) : dist (P a) (P b) ≤ B := by
    exact Finset.le_sup' (s := s) (f := fun ab => dist (P ab.1) (P ab.2))
      (Finset.mem_univ (a,b))
  have hBpos : 0 ≤ B := by
    let a : ι := Classical.choice inferInstance
    exact (dist_nonneg : 0 ≤ dist (P a) (P a)).trans (hB a a)
  have hBlt : B < C := by
    apply (Finset.sup'_lt_iff (s := s) hs).2
    intro ab hab
    exact h ab.1 ab.2
  have hdiam : Metric.diam (Set.range P) ≤ B := by
    apply Metric.diam_le_of_forall_dist_le hBpos
    intro x hx y hy
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact hB a b
  exact hdiam.trans_lt hBlt

/-- For every `n ≥ 68000`, one fixed `ℝ^458999` contains `n` injectively
indexed points whose distinct distances are at least one, whose unordered
edge distances differ by at least one, and whose diameter is strictly less
than `(37/50)n²`. -/
theorem fixed_dimension_erdos_670 (n : ℕ) (hn : 68000 ≤ n) :
    ∃ P : Fin n → EuclideanSpace ℝ (Fin 458999),
      Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
      SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (37 / 50 : ℝ) * (n : ℝ) ^ 2) ∧
      Metric.diam (Set.range P) < (37 / 50 : ℝ) * (n : ℝ) ^ 2 := by
  have hsource : ∀ m k : ℕ, 34000 ≤ m → m ≤ 51000 → 2 ≤ k →
      ∃ P : Fin m × Fin k → EuclideanSpace ℝ
          (ClusterCoordinate (Fin (m-1)) m),
        (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
        SeparatedConfiguration P ∧
        (∀ a b, dist (P a) (P b) ≤
          sourceMacroStep (k : ℝ) *
              ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
            sourcePerturbationBound (k : ℝ) +
            sourceError (sourceOffset m : ℝ) (k : ℝ)) := by
    intro m k hm hmup hk
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q + 2 := ⟨m - 2, by omega⟩
    obtain ⟨prime, hp, hsize, hupper⟩ :=
      source_ruler_prime_exists (q+2) k (by omega) (by omega)
    obtain ⟨P, hlocal, hcross, hdiam⟩ :=
      source_actual_ruler_configuration_metrics_diameter
        (n := q) hm hk prime
    have hsep : SeparatedConfiguration P :=
      source_separatedConfiguration_of_metrics (m := q+1)
        hm hk prime hp (by simpa only [Nat.add_assoc] using hsize)
        (by simpa only [Nat.add_assoc] using hupper) P hlocal hcross
    have hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b) :=
      source_minimum_distance_of_metrics (m := q+1)
        hm hk prime hp (by simpa only [Nat.add_assoc] using hsize)
        (by simpa only [Nat.add_assoc] using hupper) P hlocal hcross
    exact ⟨P, hmin, hsep, hdiam⟩
  obtain ⟨P, hmin, hsep, hdiam⟩ :=
    source_all_n_fixed_dimension_of_finite_sources hsource n hn
  have hinj : Function.Injective P :=
    injective_of_unit_minimum_distance P hmin
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact ⟨P, hinj, hmin, hsep, hdiam,
    finite_range_diam_lt_of_pairwise_lt P _ hdiam⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension
