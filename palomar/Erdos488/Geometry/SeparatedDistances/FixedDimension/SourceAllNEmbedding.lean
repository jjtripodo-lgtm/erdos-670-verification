module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.AllNArithmetic
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanClusterCoordinates
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceFinalScalar
public import Erdos488.Geometry.SeparatedDistances.Defs

@[expose] public section

/-! Distance-preserving deletion and coordinate padding for the all-size step. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

/-- The source's coordinate count fits in the claimed fixed dimension. -/
theorem source_cluster_coordinate_card_le_fixed {m : ℕ}
    (hm : 34000 ≤ m) (hmup : m ≤ 51000) :
    Fintype.card (ClusterCoordinate (Fin (m-1)) m) ≤ 458999 := by
  rw [clusterCoordinate_card m (by omega)]
  omega

/-- A family restricted along an injection retains its unit minimum. -/
theorem source_minimum_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (hf : Function.Injective f)
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) :
    ∀ a b, a ≠ b → 1 ≤ dist (P (f a)) (P (f b)) := by
  intro a b hab
  exact hmin _ _ (hf.ne hab)

/-- The induced map on non-diagonal unordered edges. -/
def sourceEdgeMap {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    Edge ι → Edge κ := fun e =>
  ⟨Sym2.map f e.1, (Sym2.isDiag_map hf).not.mpr e.2⟩

theorem sourceEdgeMap_injective {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) : Function.Injective (sourceEdgeMap f hf) := by
  intro e₁ e₂ h
  apply Subtype.ext
  exact (Sym2.map.injective hf) (congrArg Subtype.val h)

private theorem source_edgeDistance_map {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (e : Sym2 ι) :
    edgeDistance (P ∘ f) e = edgeDistance P (Sym2.map f e) := by
  induction e using Sym2.inductionOn with
  | hf a b => rfl

/-- Restricting a family along an injection preserves edge separation. -/
theorem source_separated_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (hf : Function.Injective f)
    (hsep : SeparatedConfiguration P) : SeparatedConfiguration (P ∘ f) := by
  intro e₁ e₂ hne
  have hne' : sourceEdgeMap f hf e₁ ≠ sourceEdgeMap f hf e₂ :=
    (sourceEdgeMap_injective f hf).ne hne
  convert hsep (sourceEdgeMap f hf e₁) (sourceEdgeMap f hf e₂) hne' using 1 <;>
    simp only [sourceEdgeMap, source_edgeDistance_map]

/-- Restriction cannot increase any pairwise distance bound. -/
theorem source_diameter_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (D : ℝ)
    (hdiam : ∀ a b, dist (P a) (P b) ≤ D) :
    ∀ a b, dist (P (f a)) (P (f b)) ≤ D := by
  intro a b
  exact hdiam _ _

/-- Extend coordinates by zero along a disjoint sum. -/
noncomputable def sourceSumPad {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ κ) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun _ => 0))

theorem sourceSumPad_dist {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : EuclideanSpace ℝ ι) :
    dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y) = dist x y := by
  have hsq : dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y)^2 =
      dist x y ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
    simp [sourceSumPad, Fintype.sum_sum_type]
  nlinarith [show 0 ≤ dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y) from dist_nonneg,
    show 0 ≤ dist x y from dist_nonneg]

/-- Pad an arbitrary finite Euclidean coordinate type into `Fin D`. -/
noncomputable def sourcePadCoordinates {ι : Type*} [Fintype ι] {D : ℕ}
    (hcard : Fintype.card ι ≤ D) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (Fin D) :=
  let e₁ := Fintype.equivFin ι
  let e₂ : Fin (Fintype.card ι) ⊕ Fin (D - Fintype.card ι) ≃
      Fin (Fintype.card ι + (D - Fintype.card ι)) := finSumFinEquiv
  let e₃ := finCongr (Nat.add_sub_of_le hcard)
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₃)
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₂)
      (sourceSumPad (κ := Fin (D - Fintype.card ι))
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₁) x)))

theorem sourcePadCoordinates_dist {ι : Type*} [Fintype ι] {D : ℕ}
    (hcard : Fintype.card ι ≤ D) (x y : EuclideanSpace ℝ ι) :
    dist (sourcePadCoordinates hcard x) (sourcePadCoordinates hcard y) = dist x y := by
  simp [sourcePadCoordinates, sourceSumPad_dist]

/-- Delete the surplus vertices by taking the first `n` positions of a finite
enumeration of the rectangular cluster grid. -/
noncomputable def sourceDeletionEmbedding {n m k : ℕ} (hsize : n ≤ m*k) :
    Fin n → Fin m × Fin k :=
  (Fintype.equivFinOfCardEq (α := Fin m × Fin k) (by simp)).symm ∘
    Fin.castLE hsize

theorem sourceDeletionEmbedding_injective {n m k : ℕ} (hsize : n ≤ m*k) :
    Function.Injective (sourceDeletionEmbedding hsize) := by
  exact (Fintype.equivFinOfCardEq (α := Fin m × Fin k) (by simp)).symm.injective.comp
    (Fin.castLE_injective hsize)

/-- Isometric coordinate padding preserves minimum, unordered-edge gaps and diameter. -/
theorem source_pad_properties {ι κ : Type*} [Fintype κ] {D : ℕ}
    (hcard : Fintype.card κ ≤ D) (P : ι → EuclideanSpace ℝ κ)
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : SeparatedConfiguration P) (B : ℝ)
    (hdiam : ∀ a b, dist (P a) (P b) ≤ B) :
    (∀ a b, a ≠ b → 1 ≤ dist (sourcePadCoordinates hcard (P a))
      (sourcePadCoordinates hcard (P b))) ∧
    SeparatedConfiguration (sourcePadCoordinates hcard ∘ P) ∧
    (∀ a b, dist (sourcePadCoordinates hcard (P a))
      (sourcePadCoordinates hcard (P b)) ≤ B) := by
  constructor
  · intro a b hab
    rw [sourcePadCoordinates_dist]
    exact hmin a b hab
  constructor
  · intro e₁ e₂ hne
    induction e₁ using Subtype.rec with
    | _ s hs =>
      induction e₂ using Subtype.rec with
      | _ t ht =>
        induction s using Sym2.inductionOn with
        | hf a b =>
          induction t using Sym2.inductionOn with
          | hf c d =>
            simpa only [edgeDistance, Sym2.lift_mk, Function.comp_apply,
              sourcePadCoordinates_dist] using hsep ⟨s(a,b),hs⟩ ⟨s(c,d),ht⟩ hne
  · intro a b
    rw [sourcePadCoordinates_dist]
    exact hdiam a b

/-- The finite source's three metric properties pass to exactly `n` points
in the same fixed ambient space. The finite source facts are explicit hypotheses. -/
theorem source_delete_pad_fixed_dimension {n m k : ℕ}
    (hn : 68000 ≤ n) (hm : 34000 ≤ m) (hmup : m ≤ 51000)
    (hk : 2 ≤ k) (hsize : n ≤ m*k) (hsurplus : m*k < n+k)
    (hkbound : 34000*k ≤ n)
    (P : Fin m × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin (m-1)) m))
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : SeparatedConfiguration P)
    (hdiam : ∀ a b, dist (P a) (P b) ≤
      sourceMacroStep (k : ℝ) *
          ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
        sourcePerturbationBound (k : ℝ) +
        sourceError (sourceOffset m : ℝ) (k : ℝ)) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin 458999),
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      SeparatedConfiguration Q ∧
      (∀ a b, dist (Q a) (Q b) < (37/50 : ℝ)*(n:ℝ)^2) := by
  let f := sourceDeletionEmbedding hsize
  have hf : Function.Injective f := sourceDeletionEmbedding_injective hsize
  let hc := source_cluster_coordinate_card_le_fixed hm hmup
  let B := sourceMacroStep (k : ℝ) *
          ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
        sourcePerturbationBound (k : ℝ) +
        sourceError (sourceOffset m : ℝ) (k : ℝ)
  have hmin' := source_minimum_restrict P f hf hmin
  have hsep' := source_separated_restrict P f hf hsep
  have hdiam' := source_diameter_restrict P f B hdiam
  obtain ⟨hminQ, hsepQ, hdiamQ⟩ :=
    source_pad_properties hc (P ∘ f) hmin' hsep' B hdiam'
  refine ⟨sourcePadCoordinates hc ∘ P ∘ f, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hminQ
  · simpa only [Function.comp_assoc] using hsepQ
  · intro a b
    have hbound := source_rounded_diameter_lt n m k hn hm hk hsurplus hkbound
    exact lt_of_le_of_lt (by simpa only [Function.comp_apply] using hdiamQ a b) hbound

/-- Honest all-`n` interface: a finite source at each rectangular parameter
supplies the three geometric facts, and this theorem performs the rounding,
deletion and zero-coordinate embedding. -/
theorem source_all_n_fixed_dimension_of_finite_sources
    (hsource : ∀ m k : ℕ, 34000 ≤ m → m ≤ 51000 → 2 ≤ k →
      ∃ P : Fin m × Fin k → EuclideanSpace ℝ
          (ClusterCoordinate (Fin (m-1)) m),
        (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
        SeparatedConfiguration P ∧
        (∀ a b, dist (P a) (P b) ≤
          sourceMacroStep (k : ℝ) *
              ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
            sourcePerturbationBound (k : ℝ) +
            sourceError (sourceOffset m : ℝ) (k : ℝ))) :
    ∀ n : ℕ, 68000 ≤ n →
      ∃ Q : Fin n → EuclideanSpace ℝ (Fin 458999),
        (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
        SeparatedConfiguration Q ∧
        (∀ a b, dist (Q a) (Q b) < (37/50 : ℝ)*(n:ℝ)^2) := by
  intro n hn
  obtain ⟨k, m, hk, hm, hmup, hsize, hsurplus, hkbound⟩ :=
    every_large_n_cluster_parameters n hn
  obtain ⟨P, hmin, hsep, hdiam⟩ := hsource m k hm hmup hk
  exact source_delete_pad_fixed_dimension hn hm hmup hk hsize hsurplus hkbound
    P hmin hsep hdiam

end Erdos488.Geometry.SeparatedDistances.FixedDimension
